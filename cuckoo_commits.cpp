#include <algorithm>
#include <atomic>
#include <assert.h>
#include <chrono>
#include <iostream>
#include <fstream>
#include <math.h>
#include <stdlib.h>
#include <thread>
#include <time.h>
#include <stdint.h>
#include <vector>
#include <unistd.h>
using namespace std;


#define bin_size 8
#define bin_num (1<<14L)
#define threads (uint64_t) 15
double init_fill = .95;
int inserts_per_kill = 2;
int inserts_per_read = 1;
int inserts_per_overwrite = 1;
unsigned long long batch = 100; // this many operations are done in each commit cycle
int trial_num = 100;
uint64_t maxchain = 500;
bool balance = true;
int only_cycle = 0; // 0 to run both with and without cycle-kick mode, 1 to run just cycle-kick mode
bool retry_on = true; // whether or not to do retries of verifications that a record _isn't_ present
bool live_kickout = true; // whether or not to do kickout chains as system transaction

#define klockflag (((uint64_t)1)<<32)

class cuckoo_table {
public: // all public for now
  int other_bin[bin_num][bin_size]; // pairs of hashes act as keys; for each record, this stores its other hash; empty slot --> -1
  uint64_t payloads[bin_num][bin_size]; // a payload for each slot
  atomic <int> kickout_index[bin_num]; // also known as kickout counter
  int canceled_inserts[threads][2]; // 0 -> actual count, 1 -> temporary count for current commit phase, -1 for an insert
  vector <int> pairs_inserted; // the pairs that can potentially be inserted
  std::atomic<uint64_t> slot_ids[bin_num][bin_size];
  std::atomic<uint64_t> bin_ids[bin_num];
  bool cyclekick; // whether to use cycle-kick option


  // Defining the write and read sets (which are merged as one thing here) =======================================================
  // Requirements for write set to be valid: can't modify or read same record twice in same transaction
  // (will lead to an abort). Would be easy to alleviate requirement for reads.
  // Each write_set element is required to have one of either bin id or slot id be null.
  // Whichever is not null is the id which will be verified in the verification phase.
  struct LogElt {
    uint64_t bin_;
    uint64_t slot_;
    int new_entry_; // the other hashed bin
    cuckoo_table* owner_;
    std::atomic<uint64_t> *slot_id_;
    std::atomic<uint64_t> *bin_id_;
    uint64_t expected_slot_id_;
    uint64_t expected_bin_id_;
    bool for_write_;
    bool just_lock_bin_;

    uint64_t expected_payload_;
    uint64_t new_payload_;

    LogElt (uint64_t bin, uint64_t slot, int new_entry, uint64_t expected_bin_id,
	    uint64_t expected_slot_id, std::atomic <uint64_t>* current_bin_id,
	    std::atomic <uint64_t>* current_slot_id, uint64_t expected_payload,
	    uint64_t new_payload,
	    bool for_write, cuckoo_table* owner) {
      bin_ = bin;
      slot_ = slot;
      new_entry_ = new_entry;
      expected_bin_id_ = expected_bin_id;
      expected_slot_id_ = expected_slot_id;
      expected_payload_ = expected_payload;
      new_payload_ = new_payload;
      owner_ = owner;
      for_write_ = for_write;
      bin_id_ = current_bin_id;
      slot_id_ = current_slot_id;
      just_lock_bin_ = false;
      assert((expected_bin_id & klockflag) == 0);
      assert((expected_slot_id & klockflag) == 0);
    }

    LogElt (int bin, int slot, int new_entry, uint64_t expected_bin_id,
	    uint64_t expected_slot_id, uint64_t expected_payload,
	    uint64_t new_payload,
	    bool for_write, cuckoo_table* owner) {
      bin_ = bin;
      slot_ = slot;
      new_entry_ = new_entry;
      expected_bin_id_ = expected_bin_id;
      expected_slot_id_ = expected_slot_id;
      owner_ = owner;
      for_write_ = for_write;
      bin_id_ = &(owner_->bin_ids[bin_]);
      expected_payload_ = expected_payload;
      new_payload_ = new_payload;
      slot_id_ = &(owner_->slot_ids[bin_][slot_]);
      just_lock_bin_ = false;
      assert((expected_bin_id & klockflag) == 0);
      assert((expected_slot_id & klockflag) == 0);
    }

    LogElt () {
    }

    void get_lock_unconditional(bool already_done) { // locks bin unconditionally
      assert(slot_id_ == nullptr);
      if (already_done) {
	expected_bin_id_ = *bin_id_ - klockflag;
	return;
      }
      bool grabbed = false;
      while (!grabbed) {
	expected_bin_id_ = *bin_id_;
	while ((expected_bin_id_ & klockflag) != 0) expected_bin_id_ = *bin_id_;
	// ---------------------------------------------------- SHOULD DO SOME SORT OF PAUSE IN ABOVE LOOP -------------------------------------
	uint64_t id_guess = expected_bin_id_;
	grabbed = (*bin_id_).compare_exchange_weak(id_guess, id_guess | klockflag);
      }
    }

    // Verifies and locks appropriate id. NOTE: retry is not done here in this version.
    // For reads, just does normal conditional check.
    bool conditional_lock (bool already_locked) { // locks if the id hasn't changed
      assert((expected_bin_id_ & klockflag) == 0);
      assert((expected_slot_id_ & klockflag) == 0);
      if (bin_id_ != nullptr && for_write_ && !already_locked) {
	uint64_t bin_id_guess = expected_bin_id_;
	bool success = (*bin_id_).compare_exchange_weak(bin_id_guess, expected_bin_id_ | klockflag);
	//if (!success) cout<<"bin abort----------------------"<<endl;
	if (!success) return false;
	//cout<<"Bin didn't abort"<<endl;
      }
      if (bin_id_ != nullptr && for_write_ && already_locked) {
	if (((uint64_t)(*bin_id_) | klockflag) != (expected_bin_id_ | klockflag)) return false;
      }
      if (slot_id_ != nullptr && for_write_) {
	uint64_t slot_id_guess = expected_slot_id_;
	bool success = (*slot_id_).compare_exchange_weak(expected_slot_id_, expected_slot_id_ | klockflag);
	//if (!success) cout<<"slot abort-------------------"<<endl;
	if (!success) {
	  if (bin_id_ != nullptr && for_write_ && !already_locked) *bin_id_ = *bin_id_ - klockflag; // need to unlock!
	  return false;
	}
	assert(expected_payload_ == owner_->payloads[bin_][slot_]);
	// confirms that overwrites are working the way they're supposed to.
	// which is equivalent to reads working the way they're supposed to.
      }
      if (bin_id_ != nullptr && !for_write_ && ((uint64_t)(*bin_id_)) != (expected_bin_id_)) {
	if (already_locked) {
	  if (((uint64_t)(*bin_id_) | klockflag) != (expected_bin_id_ | klockflag)) return false;
	}
	if (!already_locked) return false;
      }
      if (slot_id_ != nullptr && !for_write_ && ((uint64_t)(*slot_id_)) != (expected_slot_id_)) {
	//cout<<"Canceled"<<endl;
	return false;
      }
      return true;
    }

    void apply (uint64_t new_id) { // applies with new id which should be maximum of ids in write set
      if (for_write_) {
	assert((slot_ >= 0 || slot_ <= bin_size) && (bin_ >= 0 || bin_ < bin_num));
	uint64_t temp_id = new_id | klockflag;
	if (bin_id_ != nullptr) {
	  assert((*bin_id_ && klockflag) != 0);
	  assert(*bin_id_ <= temp_id); // could be equal if is second time seeing bin id in transaction
	  *bin_id_ = temp_id;
	}
	if (slot_id_ != nullptr) {
	  assert((*slot_id_ && klockflag) != 0);
	  assert(*slot_id_ < temp_id);
	  *slot_id_ = temp_id;
	  owner_->other_bin[bin_][slot_] = new_entry_;
	  owner_->payloads[bin_][slot_] = new_payload_;
	}
      }
    }

    void unlock (bool unlock_bin) { // unlocks
      if (for_write_) {
	if (bin_id_ != nullptr && unlock_bin) {
	  assert((*bin_id_ & klockflag) != 0);
	  *bin_id_ = *bin_id_ - klockflag;
	}
	if (slot_id_ != nullptr) {
	  assert((*slot_id_ & klockflag) != 0);
	  *slot_id_ = *slot_id_ - klockflag;
	}
      }
    }

    // so we can get a global locking order // bin id, then slot id, then whether for write
    // bins before slots because when we do a retry on a bin, we don't want to deadlock with our own slot lock
    // In commit phase, need to do for writes first for serializability
    static bool compare(const LogElt &left, const LogElt &right) {
      if (left.bin_id_ != right.bin_id_) return (left.bin_id_ > right.bin_id_); // Very important nulls go last, that way bins come before slots.
      if (left.slot_id_ != right.slot_id_) return (left.slot_id_ < right.slot_id_); 
      return (left.for_write_ > right.for_write_); // reads after writes
    }
  };

  // The commit protocol =============================================================
  void abort  (vector <LogElt> write_set, int locked_index) { // Uses pre-sorted write set
    for (int x = 0; x < locked_index; x++) {
      bool prev_bin_id_same = false; // allows us to avoid unlocking same bin twice
      if (write_set[x].bin_id_ != nullptr) {
	int first_hit = x;
	while (first_hit >= 0 && write_set[first_hit].bin_id_ == write_set[x].bin_id_) first_hit--;
	first_hit++; // subtracted one too much
	if (first_hit < x && write_set[first_hit].for_write_) {
	  prev_bin_id_same = true;
	}
      }
      write_set[x].unlock(!prev_bin_id_same);
    }
  }

  bool is_unlocked(vector <LogElt> write_set) { // only used for single-thread testing!
    for (uint64_t x = 0; x < write_set.size(); x++) {
      if (write_set[x].for_write_ && slot_ids[write_set[x].bin_][write_set[x].slot_] & klockflag) return false;
      if (write_set[x].for_write_ && bin_ids[write_set[x].bin_] & klockflag) return false;
    }
    return true;
  }

  // Note: Retry was implemented here separately than in
  // cuckoo_commits2. So the implementation is slightly different.  In
  // particular, retries are all done at the very start. And then if
  // we find at some point that we need to do another retry, then we
  // just start the entire commit process over. The difference between
  // doing retries at the beginning vs while taking locks may affect
  // the speed of a small number of commits (since if a retry sneaks
  // in between when we check for retries and when we're taking locks,
  // then we have to release all locks and start over). But the
  // overall affect on aborts should not be statistically significant
  // (confirmed with a bit of playing around). I only did it
  // differently in the other version to make sure the fancier way of
  // doing it doesn't result in any unforseen deadlocks or anything.
  bool commit(vector <LogElt> &write_set, uint64_t* worker_id) {
    // // For testing only.
    // bool terminate = false;
    // for (uint64_t x = 0; x < write_set.size(); x++) { // just for sake of testing
    //   for (uint64_t y = x + 1; y < write_set.size(); y++) {
    // 	if (write_set[x].for_write_ && write_set[y].for_write_ &&
    // 	                            write_set[x].slot_id_ != nullptr && write_set[y].slot_id_ != nullptr &&
    // 	    (write_set)[x].bin_ == (write_set)[y].bin_ && (write_set)[x].slot_ == (write_set)[y].slot_) {
    // 	  terminate = true;
    // 	}
    //   }
    // }

    vector <LogElt> sorted_write_set (write_set.size());
    for (uint64_t x = 0; x < write_set.size(); x++) sorted_write_set[x] = write_set[x];
    std::stable_sort (sorted_write_set.begin(), sorted_write_set.end(), LogElt::compare);
    int set_size = sorted_write_set.size();

    // do retries now -------------------------

    if (retry_on) {
      for (int x = 0; x < write_set.size(); x++) {
	LogElt elt = sorted_write_set[x];
	if (elt.bin_id_ != nullptr && elt.slot_id_ == nullptr) { // if the id is going to be used to prove a record isn't present
	  if (*(elt.bin_id_) != elt.expected_bin_id_) {
	    assert(*(elt.bin_id_) >= elt.expected_bin_id_); // could be equal if was locked and then aborted
	    // do a retry
	    uint64_t hash1 = elt.bin_, hash2 = elt.new_entry_, bin_id = 0, slot_id = 0, slot = 0, payload = 0;
	    if (find_record(hash1, hash2, &bin_id, &slot_id, &slot, &payload)) {
	      return false; // record's state of existance changed
	    }
	    // if we didn't find the record, then we just fix the write-read set element
	    sorted_write_set[x].expected_bin_id_ = bin_id;
	  }
	}
      }
    }

    // check write set and lock. ------------------
    // lock in sorted order
    uint64_t new_id = *worker_id | klockflag;
    for (uint64_t x = 0; x < write_set.size(); x++) {
      if (sorted_write_set[x].for_write_) {
	bool prev_bin_id_same = false;
	if (sorted_write_set[x].bin_id_ != nullptr) { // need to know if we've already locked bin
	  int first_hit = x;
	  while (first_hit >= 0 && sorted_write_set[first_hit].bin_id_ == sorted_write_set[x].bin_id_) first_hit--;
	  first_hit++; // subtracted one too much
	  if (first_hit < x && sorted_write_set[first_hit].for_write_) {
	    prev_bin_id_same = true;
	  }
	}
	if (sorted_write_set[x].just_lock_bin_) {
	  sorted_write_set[x].get_lock_unconditional(prev_bin_id_same);
	} else {
	  if (!sorted_write_set[x].conditional_lock(prev_bin_id_same)) {
	    // Note that if we had a cycle in a path, this will catch it -- we're not allowed to edit the same slot twice in the same transaction
	    LogElt elt = sorted_write_set[x];
	    if (retry_on && elt.bin_id_ != nullptr && elt.slot_id_ == nullptr) {
	      abort(sorted_write_set, x); // x tells us up to what index we need to unlock
	      return commit(write_set, worker_id); // try again
	    } else {
	      abort(sorted_write_set, x); // x tells us up to what index we need to unlock
	      return false;
	    }
	  }
	}
	if (sorted_write_set[x].slot_id_ != nullptr) new_id = max(new_id | klockflag, sorted_write_set[x].expected_slot_id_ | klockflag);
	if (sorted_write_set[x].bin_id_ != nullptr) new_id = max(new_id | klockflag, sorted_write_set[x].expected_bin_id_ | klockflag);
      }
    }

    std::atomic_thread_fence(std::memory_order_release); // memory fence
    std::atomic_thread_fence(std::memory_order_acquire);

    // Now need verify read set now
    for (uint64_t x = 0; x < write_set.size(); x++) {
      if (!sorted_write_set[x].for_write_) {
	bool prev_bin_id_same = false;
	if (sorted_write_set[x].bin_id_ != nullptr) { // need to know if we've already locked bin
	  int first_hit = x;
	  while (first_hit >= 0 && sorted_write_set[first_hit].bin_id_ == sorted_write_set[x].bin_id_) first_hit--;
	  first_hit++; // subtracted one too much
	  if (first_hit < x && sorted_write_set[first_hit].for_write_) {
	    prev_bin_id_same = true;
	  }
	}
	if (!sorted_write_set[x].conditional_lock(prev_bin_id_same)) {
	  LogElt elt = sorted_write_set[x];
	  if (retry_on && elt.bin_id_ != nullptr && elt.slot_id_ == nullptr) {
	    abort(sorted_write_set, sorted_write_set.size()); 
	    return commit(write_set, worker_id); // try again
	  } else {
	    abort(sorted_write_set, sorted_write_set.size()); 
	    return false;
	  }
	}
	if (sorted_write_set[x].slot_id_ != nullptr) new_id = max(new_id | klockflag, sorted_write_set[x].expected_slot_id_ | klockflag);
	if (sorted_write_set[x].bin_id_ != nullptr) new_id = max(new_id | klockflag, sorted_write_set[x].expected_bin_id_ | klockflag);
      }
    }
    new_id++;
    //    assert(!terminate);

    // apply in actual order
    for (uint64_t x = 0; x < write_set.size(); x++) write_set[x].apply(new_id);
    std::atomic_thread_fence(std::memory_order_release); // memory fence
    std::atomic_thread_fence(std::memory_order_acquire);


    // unlock in sorted order
    for (uint64_t x = 0; x < write_set.size(); x++) {
      bool prev_bin_id_same = false;
      if (sorted_write_set[x].bin_id_ != nullptr) {
	int first_hit = x;
	while (first_hit >= 0 && sorted_write_set[first_hit].bin_id_ == sorted_write_set[x].bin_id_) first_hit--;
	first_hit++; // subtracted one too much
	if (first_hit < x && sorted_write_set[first_hit].for_write_) {
	  prev_bin_id_same = true;
	}
      }
      sorted_write_set[x].unlock(!prev_bin_id_same);
    }
    for (uint64_t x = 0; x < write_set.size(); x++)
      if (write_set[x].for_write_ && write_set[x].slot_id_ != nullptr)
	assert(write_set[x].expected_slot_id_ < new_id);
    //assert(is_unlocked(write_set)); // just for single-threaded case
    //cout<<"Not aborted"<<endl;
    *worker_id = new_id - klockflag;
    return true;
  }

  // Actual hash table stuff ======================================================


  int first_empty_position(int bucket) { //First empty position if bucket is not full; -1 if bucket is full.
    for (int x = 0; x < bin_size; x++) {
      if (other_bin[bucket][x] == -1 && (slot_ids[bucket][x] & klockflag) == 0) return x;
    }
    return -1;
  }

  // Here we pick which element to kick out of the bucket
  int pick_slot(int bucket) {
    if (cyclekick) {
      int answer = kickout_index[bucket];
      kickout_index[bucket]++;
      //int answer = atomic_fetch_add(&kickout_index[bucket], 1);
      return answer % bin_size;
    }
    int answer = rand() % bin_size; // random walk strategy (simplest and most standard strategy)
    int temp = 0;
    while (other_bin[bucket][answer] != -1 && first_empty_position(bucket) != -1) {
      answer = rand() % bin_size;
      temp++;
    }
    return answer;
  }

  /// Here we pick which of the two hashed to buckets to insert into. Returns one of the two choices.
  int pick_bucket(int choice1, int choice2, int *touches) {
    if (balance) return pick_bucket_balance(choice1, choice2, touches);
    // The standard way of doing it
    *touches=*touches+1;
    if(first_empty_position(choice1)>=0) return choice1;
    *touches=*touches+1;
    if(first_empty_position(choice2)>=0) return choice2;
    return choice2;
  }

  int pick_bucket_balance(int choice1, int choice2, int *touches) { //Sticks in emptier of the two buckets
    *touches+=2;
    int size1=0, size2=0;
    for(int x=0; x<bin_size; x++) {
      if(other_bin[choice1][x]!=-1) size1++; // don't worry baut locks here
      if(other_bin[choice2][x]!=-1) size2++;
    }
    if(size2 < size1) return choice2;
    return choice1;
  }

  void get_bin_id_unlocked(uint64_t* bin_id, int bin) {
    int temp = 0;
    *bin_id = bin_ids[bin];
    while ((*bin_id & klockflag) != 0) {
      // ---------------------------------------------------- SHOULD DO SOME SORT OF PAUSE HERE -------------------------------------
      *bin_id = bin_ids[bin];
      temp++;
    }
  }

  void get_slot_id_unlocked(uint64_t* slot_id, int bin, int slot) {
    *slot_id = slot_ids[bin][slot];
    while ((*slot_id & klockflag) != 0) {
      // ---------------------------------------------------- SHOULD DO SOME SORT OF PAUSE HERE -------------------------------------
      *slot_id = slot_ids[bin][slot];
    }
  }

  int find_record(int bucket, int load, uint64_t* bin_id_chosen,
		  uint64_t* slot_id_chosen, uint64_t* slot, uint64_t* payload) {
    uint64_t bin_id;
    uint64_t hash1 = bucket, hash2 = load;
    uint64_t temp_payload = 0;
    get_bin_id_unlocked(&bin_id, hash1); // get unlocked bin id
    assert((bin_id & klockflag) == 0);
    *bin_id_chosen = bin_id;
    assert((*bin_id_chosen & klockflag) == 0);
    std::atomic_thread_fence(std::memory_order_release); // memory fence
    std::atomic_thread_fence(std::memory_order_acquire);
    for (int x = 0; x < bin_size; x++) {
      // getting the slot entry:
      uint64_t slot_id;
      uint64_t slot_entry;
      get_slot_id_unlocked(&slot_id, hash1, x); // get unlocked slot id
      std::atomic_thread_fence(std::memory_order_release); // memory fence
      std::atomic_thread_fence(std::memory_order_acquire);
      // get slot entry
      slot_entry = other_bin[hash1][x];
      temp_payload = payloads[hash1][x];
      std::atomic_thread_fence(std::memory_order_release); // memory fence
      std::atomic_thread_fence(std::memory_order_acquire);
      // verify that slot id is still the same
      // needs to be done because we're not allowed to read a locked slot
      if (slot_ids[hash1][x] != slot_id) {
	x--; // have to retry
      } else {
	if (slot_entry == hash2) {
	  *slot = x;
	  *payload = temp_payload;
	  *slot_id_chosen = slot_id;
	  return true;
	}
      }
    }
    return false;
  }

  int chain(int bucket, int other_hash, int depth, vector <LogElt>* write_set, int thread_id,
	    uint64_t payload_entry) { // Inserts -- goes down Cuckoo Chain as needed; returns length of resulting Cuckoo Chain.
    if ((uint64_t) depth > maxchain) {
      assert(1 == 2);
      cout<<"LEGIT ABORT"<<endl;
      return 0;
    }
    //cout<<"Insert attempt"<<endl;
    uint64_t slot_id, bin_id1 = 0, bin_id2 = 0, slot, payload = 0;
    if (depth == 0) { // check if already inserted
      bool quit1 = false, quit2 = false;
      if (find_record(bucket, other_hash, &bin_id1, &slot_id, &slot, &payload)) quit1 = true;
      assert((bin_id1 & klockflag) == 0);
      if (find_record(other_hash, bucket, &bin_id2, &slot_id, &slot, &payload)) quit2 = true;
      assert((bin_id2 & klockflag) == 0);
      if (quit1 || quit2) {
	LogElt new_entry1 = LogElt(bucket, slot, other_hash, 0, slot_id, nullptr, &slot_ids[bucket][slot],
				   payload, payload, false, this);
	LogElt new_entry2 = LogElt(other_hash, slot, bucket, 0, slot_id, nullptr, &slot_ids[other_hash][slot],
				   payload, payload, false, this);
	if (quit1) {
	  write_set->push_back(new_entry1);
	  return 0; // don't want to push both back if are same, because transactional kickout expects this case to yield set of size 1 (doesn't matter really though)
	}
	if (quit2) {
	  write_set->push_back(new_entry2);
	  return 0;
	}
      }
      // need to verify record is not present
      LogElt entry1 = LogElt(other_hash, 0, bucket, bin_id2, 0, &bin_ids[other_hash],
			     nullptr, payload, payload, false, this); //verifying record not present
      LogElt entry2 = LogElt(bucket, 0, other_hash, bin_id1, 0, &bin_ids[bucket],
			     nullptr, payload, payload, true, this); // this one is in write set
      write_set->push_back(entry1);
      write_set->push_back(entry2);
    }
    if (depth == 0) canceled_inserts[thread_id][1]--; // is negative the number of records added by thread
    int temp = 0;
    bool valid_slot = false;
    while (!valid_slot) { // need to get valid slot
      slot = pick_slot(bucket);
      temp++;
      if (temp > 100000) cout<<"Lots of waiting..."<<endl;
      slot_id = slot_ids[bucket][slot];
      valid_slot = true;
      std::atomic_thread_fence(std::memory_order_release); // memory fence so that payload is taken after
      std::atomic_thread_fence(std::memory_order_acquire);
      payload = payloads[bucket][slot];
      // payload is taken after slot id, so it may not be right. But if it isn't, we will abort because of the id change
      if ((slot_id & klockflag) > 0) valid_slot = false;
      //      cout<<temp<<endl;
    }
    LogElt new_entry = LogElt(bucket, slot, other_hash, bin_id1, slot_id, payload,
			      payload_entry, true, this); // new payload randomly generated
    LogElt bin_entry = new_entry;
    new_entry.bin_id_ = nullptr; // it's already in write set
    bin_entry.slot_id_ = nullptr;
    bin_entry.just_lock_bin_ = true;
    if (depth > 0) write_set->push_back(bin_entry); // that way bin id will be updated

    write_set->push_back(new_entry);
    std::atomic_thread_fence(std::memory_order_release);
    std::atomic_thread_fence(std::memory_order_acquire);
    if(other_bin[bucket][slot] == -1) {
      return 0;
    } else {
      int kickout = slot;
      int hash1 = other_bin[bucket][kickout];
      int hash2 = bucket;
      int answer = chain(hash1, hash2, depth+1, write_set, thread_id, payload);
      return answer+1;
    }
  }

  int insert(int hash1, int hash2, vector <LogElt>* write_set, int thread_id) { //returns length of Cuckoo chain used //inserts a random pair of hash functions
    //cout<<"made it to first insert"<<endl;
    int touches=0;
    int bucket = pick_bucket(hash1, hash2, &touches);
    int answer = 0;
    uint64_t new_payload = rand() % (1<<10);
    if(bucket == hash1) answer = touches + chain(bucket, hash2, 0, write_set, thread_id,
						 new_payload);
    if(bucket == hash2 && hash1 != hash2) answer = touches + chain(bucket, hash1, 0, write_set,
								   thread_id, new_payload);
    return answer;
  }

  // insert that performs kickout chains as system transactions. Gives kickout chain its own commit cycle
  void insert_live_kickout(int hash1, int hash2, vector <LogElt>* write_set, int thread_id) {
    int touches=0;
    int bucket = pick_bucket(hash1, hash2, &touches);
    uint64_t new_payload = rand() % (1<<10);
    bool finished = false;
    int temp = 0;
    while (1) {
      temp++;
      if (temp > 20) assert(3.14 == 3);
      vector <LogElt> write_set2(0);
      if(bucket == hash1) chain(bucket, hash2, 0, &write_set2, thread_id, new_payload);
      if(bucket == hash2 && hash1 != hash2) chain(bucket, hash1, 0, &write_set2, thread_id, new_payload);
      if (write_set2.size() == 1) { // if insert was a duplicate
	write_set->push_back(write_set2[0]);
	return;
      }
      LogElt elt1 = write_set2[0];
      LogElt elt2 = write_set2[1];
      LogElt elt3 = write_set2[2];
      write_set2.erase(write_set2.begin());
      write_set2.erase(write_set2.begin()); // doesn't need to update bin id for effectively a delete
      uint64_t new_id = 0;
      write_set2[0].new_entry_ = -1;
      write_set2[0].new_payload_ = 0;
      finished = commit(write_set2, &new_id); // system transactions get worker id 0 -- would be easy to change
      elt3.expected_slot_id_ = new_id;
      elt3.expected_payload_ = 0;
      if (finished) {
	write_set->push_back(elt1);
	write_set->push_back(elt2);
	write_set->push_back(elt3);
	return;
      }
      canceled_inserts[thread_id][1]++; // because insert failed this time -- need to retry
    }
  }

  void kill(int hash1, int hash2, vector <LogElt>* write_set, int thread_id) {
    uint64_t slot_id, bin_id1 = 0, bin_id2, slot, payload = 0;
    if (find_record(hash1, hash2, &bin_id1, &slot_id, &slot, &payload)) {
      LogElt entry = LogElt(hash1, slot, -1, bin_id1, slot_id, payload, 0, true, this);
      entry.bin_id_ = nullptr;
      write_set->push_back(entry);
      canceled_inserts[thread_id][1]++;
      return; // doesn't need to update bin id
    }
    if (find_record(hash2, hash1, &bin_id2, &slot_id, &slot, &payload)) {
      LogElt entry = LogElt(hash2, slot, -1, bin_id2, slot_id, payload, 0, true, this);
      entry.bin_id_ = nullptr;
      write_set->push_back(entry);
      canceled_inserts[thread_id][1]++;
      return; // doesn't need to update bin id
    }
    LogElt new_entry1 = LogElt(hash1, 0, hash2, bin_id1, 0, &bin_ids[hash1], nullptr,
			       0, 0, false, this);
    LogElt new_entry2 = LogElt(hash2, 0, hash1, bin_id2, 0, &bin_ids[hash2], nullptr,
			       0, 0 , false, this);
    write_set->push_back(new_entry1);
    write_set->push_back(new_entry2);
  }

  // acts as overwrite simulation
  void increment_payload(int hash1, int hash2, vector <LogElt>* write_set, int thread_id) {
    uint64_t slot_id, bin_id1 = 0, bin_id2, slot, payload = 0;
    if (find_record(hash1, hash2, &bin_id1, &slot_id, &slot, &payload)) {
      LogElt entry = LogElt(hash1, slot, hash2, bin_id1, slot_id, payload, payload + 1, true, this);
      entry.bin_id_ = nullptr;
      write_set->push_back(entry);
      return; // doesn't need to update bin id
    }
    if (find_record(hash2, hash1, &bin_id2, &slot_id, &slot, &payload)) {
      LogElt entry = LogElt(hash2, slot, hash1, bin_id2, slot_id, payload, payload + 1, true, this);
      entry.bin_id_ = nullptr;
      write_set->push_back(entry);
      return; // doesn't need to update bin id
    }
    LogElt new_entry1 = LogElt(hash1, 0, hash2, bin_id1, 0, &bin_ids[hash1], nullptr,
			       0, 0, false, this);
    LogElt new_entry2 = LogElt(hash2, 0, hash1, bin_id2, 0, &bin_ids[hash2], nullptr,
			       0, 0 , false, this);
    write_set->push_back(new_entry1);
    write_set->push_back(new_entry2);
  }

  // just very slightly changed overwrite
  void read(int hash1, int hash2, vector <LogElt>* write_set, int thread_id) {
    uint64_t slot_id, bin_id1 = 0, bin_id2, slot, payload = 0;
    if (find_record(hash1, hash2, &bin_id1, &slot_id, &slot, &payload)) {
      LogElt entry = LogElt(hash1, slot, hash2, bin_id1, slot_id, payload, payload, false, this);
      entry.bin_id_ = nullptr;
      write_set->push_back(entry);
      return;
    }
    if (find_record(hash2, hash1, &bin_id2, &slot_id, &slot, &payload)) {
      LogElt entry = LogElt(hash2, slot, hash1, bin_id2, slot_id, payload, payload, false, this);
      entry.bin_id_ = nullptr;
      write_set->push_back(entry);
      return;
    }
    LogElt new_entry1 = LogElt(hash1, 0, hash2, bin_id1, 0, &bin_ids[hash1], nullptr,
			       0, 0, false, this);
    LogElt new_entry2 = LogElt(hash2, 0, hash1, bin_id2, 0, &bin_ids[hash2], nullptr,
			       0, 0 , false, this);
    write_set->push_back(new_entry1);
    write_set->push_back(new_entry2);
  }

  bool transaction_check (vector <int>* transaction_pairs, int a, int b) {
    // checks for no repeats
    for (uint64_t r = 0; r < transaction_pairs->size() / 2; r++) {
      if ((*transaction_pairs)[2*r] == a && (*transaction_pairs)[2*r+1] == b) {
	return false;
      }
      if ((*transaction_pairs)[2*r] == b && (*transaction_pairs)[2*r+1] == a) {
	return false;
      }
    }
    transaction_pairs->push_back(a);
    transaction_pairs->push_back(b);
    return true;
  }

  // represents an individual operation called for by user
  struct Op {
    int hash1_;
    int hash2_;
    int operation_type_;
    Op(int hash1, int hash2, int op_type) {
      if (hash1 < hash2) {
	hash1_ = hash1;
	hash2_ = hash2;
      } else {
	hash2_ = hash1;
	hash1_ = hash2;
      }
      operation_type_ = op_type; // 1 -> read, 2 -> delete, 3 -> overwrite, 4 -> insert
    }
    Op() {
      hash1_ = -1;
      hash2_ = -1;
      operation_type_ = -1;
    }
  };

  // does operations assigned to a particular thread=
  void run_thread (int *pairs, int inserts, int* local_aborts, int thread_id) { // does the inserts assigned to the thread
    vector <LogElt> write_set;
    int times_tried = 0;
    int number_used = 0;
    uint64_t worker_id = 0;
    int x = 0;
    int prev_x = 0;
    vector <Op> operation_set(0);
    vector <int> transaction_pairs (0);

    while (canceled_inserts[thread_id][0] * -1 < inserts) {
      //build batch
      while (number_used < batch) {
	if (transaction_check(&transaction_pairs, pairs[2*x], pairs[2*x+1])) {
	  number_used++;
	  Op next = Op(pairs[2*x], pairs[2*x+1], 4);
	  operation_set.push_back(next);
	}
	if (number_used >= batch) {
	  x++;
	  break;
	}
	if (x % inserts_per_kill == 0 && prev_x > 0) {
	  int index = rand() % prev_x;
	  if (transaction_check(&transaction_pairs, pairs[2*index], pairs[2*index+1])) {
	    Op next = Op(pairs[2*index], pairs[2*index+1], 2);
	    operation_set.push_back(next);
	    number_used++;
	  }
	}
	if (number_used >= batch) {
	  x++;
	  break;
	}
	if (x % inserts_per_overwrite == 0 && prev_x > 0) {
	  int index = rand() % prev_x;
	  // be careful not to make index same for deletes and inserts because
	  // we currently abort when same slot is locked twice by our thread.
	  if (transaction_check(&transaction_pairs, pairs[2*index], pairs[2*index+1])) {
	    Op next = Op(pairs[2*index], pairs[2*index+1], 3);
	    operation_set.push_back(next);
	    number_used++;
	  }
	}
	if (number_used >= batch) {
	  x++;
	  break;
	}
	if (x % inserts_per_read == 0 && prev_x > 0) {
	  int index = rand() % prev_x;
	  if (transaction_check(&transaction_pairs, pairs[2*index], pairs[2*index+1])) {
	    Op next = Op(pairs[2*index], pairs[2*index+1], 1);
	    operation_set.push_back(next);
	    number_used++;
	  }
	}
	x++;
      }

      // build write and read sets
      for (int j = 0; j < operation_set.size(); j++) {
	Op elt = operation_set[j];
	//cout<<thread_id<<" "<<elt.hash1_<<" "<<elt.hash2_<<" "<<elt.operation_type_<<endl;
	if (elt.operation_type_ == 1) read(elt.hash1_, elt.hash2_, &write_set, thread_id);
	if (elt.operation_type_ == 2) kill(elt.hash1_, elt.hash2_, &write_set, thread_id);
	if (elt.operation_type_ == 3) increment_payload(elt.hash1_, elt.hash2_, &write_set, thread_id);
	if (elt.operation_type_ == 4 && !live_kickout) insert(elt.hash1_, elt.hash2_, &write_set, thread_id);
	if (elt.operation_type_ == 4 && live_kickout) insert_live_kickout(elt.hash1_, elt.hash2_, &write_set, thread_id);

      }

      // commit phase
      bool aborted = !commit(write_set, &worker_id);
      if (aborted) { // need to retry
	//cout<<"Attempted abort"<<endl;
	if (times_tried < 20) {
	  if (times_tried == 0) *local_aborts = *local_aborts + 1;
	  //cout<<number_used<<endl;
	  //cout<<"Went with retry"<<endl;
	  x = prev_x;
	  times_tried++;
	  if (times_tried == 15) {
	    //cout<<"Getting annoyed..."<<endl;
	  }
	} else {
	  times_tried = 0;
	  prev_x = x; // really giving up now
	  cout<<"Weirdness"<<endl;
	}
      }
      if (!aborted) {
	prev_x = x;
	canceled_inserts[thread_id][0] += canceled_inserts[thread_id][1];
	times_tried = 0;
      }
      write_set.resize(0);
      operation_set.resize(0);
      number_used = 0;
      canceled_inserts[thread_id][1] = 0;
      transaction_pairs.resize(0);
    }
  }


  // Tests that everything went through hash table like it was supposed to
  bool end_test(int total_inserts, int total_aborts) { // just to check for bugs in program
    // Now to test that everything went correctly
    cout<<"Total aborts: "<<total_aborts<<endl;
    int missing_count = 0;
    int positions_needed = total_inserts;
    for(int x=0; x<bin_num; x++) {
      assert((bin_ids[x] & klockflag) == 0);
      for(int y=0; y<bin_size; y++) {
	assert((slot_ids[x][y] & klockflag) == 0);
	if(other_bin[x][y] != -1) {
	  positions_needed--;
	}
      }
    }
    if(positions_needed != 0) cout<<"Positions lost: "<<positions_needed<<" "<<total_inserts<<endl;
    int expected_misses = pairs_inserted.size() / 2 - total_inserts;
    while(pairs_inserted.size() > 0) {
      int h1 = pairs_inserted.back();
      pairs_inserted.pop_back();
      int h2 = pairs_inserted.back();
      pairs_inserted.pop_back();
      bool passed = false;
      bool just_passed = false;
      for (int x=0; x<bin_size; x++) {
	if (other_bin[h1][x] == h2) just_passed = true;
	if (other_bin[h2][x] == h1) just_passed = true;
	if (just_passed && passed) { // no duplicate hash pairs allowed
	  cout<<"Found repeat!"<<endl;
	  return false;
	}
	if (just_passed) passed = true;
	just_passed = false;
      }
      if (!passed) missing_count ++;
    }
    if(missing_count <= expected_misses) return true; //when #deletes = #inserts, this is a good test of deletes
    cout<<"Elements lost! "<<missing_count<<" "<<expected_misses<<endl;
    return false;
  }

  int run() {
    //cout<<"made it to prefill"<<endl;
    uint64_t inserts = (uint64_t)(init_fill * (double)(bin_size * bin_num)) * 2; // have twice as many as desired prepared
        int **hash_pairs = new int*[threads];
    for (int i = 0; i < threads; i++) {
      hash_pairs[i] = new int[inserts / threads * 2];
    }
    //int hash_pairs [threads][inserts / threads][2];
    for (uint64_t t  = 0; t < threads; t ++) {
      for (uint64_t pair = 0; pair < inserts / threads; pair++) {
	hash_pairs[t][pair * 2] = rand() % bin_num;
	hash_pairs[t][pair * 2 + 1] = rand() % bin_num;
	pairs_inserted.push_back(hash_pairs[t][pair * 2]);
	pairs_inserted.push_back(hash_pairs[t][pair * 2 + 1]);
      }
    }
    int* aborts_table = new int[threads];
    for (uint64_t x = 0; x < threads; x++) aborts_table[x] = 0;
    vector <std::thread*> thread_array;
    /// good link: http://stackoverflow.com/questions/10673585/start-thread-with-member-function

    for (uint64_t y  = 0; y < threads; y ++) {
      thread_array.push_back(new thread(&cuckoo_table::run_thread, this, &hash_pairs[y][0], inserts / threads / 2, aborts_table + y, y));
    }
    for (uint64_t y  = 0; y < threads; y ++) {
      thread_array[y]->join();
    }

    int total_aborts = 0;
    int total_inserts = 0;
    for (uint64_t y = 0; y < threads; y++) total_aborts += aborts_table[y];
    for (uint64_t y = 0; y < threads; y++) total_inserts -= canceled_inserts[y][0];
    assert(end_test(total_inserts, total_aborts));
    //cout<<"made it!"<<endl;
    for (uint64_t y  = 0; y < threads; y ++) {
      delete thread_array[y];
    }
    delete[] aborts_table;
    return total_aborts;
  }

  cuckoo_table() { //Initializes empty table
    cyclekick=false;
    pairs_inserted.resize(0);
    for (int x = 0; x < threads; x++) {
      canceled_inserts[x][0] = 0;
      canceled_inserts[x][0] = 0;
    }
    for(int x=0; x< bin_num; x++) {
      kickout_index[x]=0;
      bin_ids[x] = 0;
      for(int y=0; y<bin_size; y++) {
	other_bin[x][y] = -1;
	payloads[x][y] = 0;
	slot_ids[x][y] = 0;
      }
    }
  }
};



double getav(vector<int> array) {
  double total = 0;
  for(uint64_t x=0; x<array.size(); x++) total += (double) array[x];
  return total / (double)array.size();
}

int getmax(vector<int> array) {
  int answer = -1;
  for(uint64_t x=0; x<array.size(); x++)
    if(array[x] > answer) answer = array[x];
  return answer;
}

int main() {
  srand (time(NULL)); //Initialize random seed
  //srand (0); //Initialize random seed
  for(int type = only_cycle; type < 2; type++) {
    cout<<"----------"<<endl;
    vector <int> aborts(trial_num);
    double av_collisions = 0;
    for(int trial=0; trial < trial_num; trial++) {
      cuckoo_table *table1 = new cuckoo_table();
      if (type == 0) table1->cyclekick = false;
      if (type == 1) table1->cyclekick = true;
      aborts[trial] = table1->run();
      delete table1;
    }
    cout<<" bin size: "<<bin_size
	<<" bin number: "<<bin_num
	<<" threads: "<<threads
	<<" init fill: "<<init_fill
	<<" inserts per kill: "<<inserts_per_kill
	<<" inserts per read: "<<inserts_per_read
	<<" inserts per overwrite "<<inserts_per_overwrite
	<<" batching: "<<batch
	<<" trials: "<<trial_num
	<<" max chain: "<<maxchain
	<<" balance on: "<<balance
	<<" cycle-kick on: "<<type<<endl;
    cout<<"Average aborts: "<<getav(aborts)<<endl;
  }
  return 0;
}

