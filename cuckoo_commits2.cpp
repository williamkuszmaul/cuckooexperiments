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


// Good memory fence source: http://preshing.com/20130922/acquire-and-release-fences/

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
int only_cycle = 0; // 0 to run both with and without fancy-mode, 1 to run just fancy-mode)
bool retry_on = true; // whether or not to do retries of verifications that a record _isn't_ present
bool live_kickout = true; // whether or not to do kickout chains as system transaction

int fancy = 0;
// 0 --> kickout counter // Actually, 0 is your only option :P

#define klockflag (((uint64_t)1)<<31)
#define kclaimflag (((uint64_t)1)<<32)

class cuckoo_table {
public: // all public for now
  int other_bin[bin_num][bin_size]; // pairs of hashes act as keys; for each record, this stores its other hash; empty slot --> -1
  uint64_t payloads[bin_num][bin_size]; // a payload for each slot
  atomic <int> kickout_index[bin_num]; // also known as kickout counter
  int canceled_inserts[threads][2]; // 0 -> actual count, 1 -> temporary count for current commit phase, -1 for an insert
  vector <int> pairs_inserted; // the pairs that can potentially be inserted
  std::atomic<uint64_t> slot_ids[bin_num][bin_size];
  std::atomic<uint64_t> bin_ids[bin_num];
  bool cyclekick;

  // Defining the write and read sets (which are merged as one thing here) =======================================================
  // Requirements for write set to be valid: can't modify/read same record twice in same transaction
  // (will lead to an abort). Would be easy to alleviate requirement for reads.
  // each write_set element is required to have one of either bin id or slot id be nul.
  struct LogElt {
    uint64_t bin_;
    uint64_t slot_;
    int new_entry_; // the other hashed bin
    cuckoo_table* owner_;
    bool special_fancy_; // whether or not we need to do something special in case of abort
    std::atomic<uint64_t> *slot_id_;
    std::atomic<uint64_t> *bin_id_;
    uint64_t expected_slot_id_;
    uint64_t expected_bin_id_;
    bool for_write_;
    bool just_lock_bin_; // for when we want to lock bin unconditionally

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
      expected_slot_id_ = (expected_slot_id | kclaimflag);
      expected_payload_ = expected_payload;
      new_payload_ = new_payload;
      owner_ = owner;
      for_write_ = for_write;
      bin_id_ = current_bin_id;
      slot_id_ = current_slot_id;
      special_fancy_ = false;
      assert((expected_bin_id & klockflag) == 0);
      assert((expected_slot_id & klockflag) == 0);
      just_lock_bin_ = false;
    }

    LogElt (int bin, int slot, int new_entry, uint64_t expected_bin_id,
	    uint64_t expected_slot_id, uint64_t expected_payload,
	    uint64_t new_payload,
	    bool for_write, cuckoo_table* owner) {
      bin_ = bin;
      slot_ = slot;
      new_entry_ = new_entry;
      expected_bin_id_ = expected_bin_id;
      expected_slot_id_ = (expected_slot_id | kclaimflag);
      owner_ = owner;
      for_write_ = for_write;
      bin_id_ = &(owner_->bin_ids[bin_]);
      //bin_id_ = nullptr; // if you want to turn off bin ids
      expected_payload_ = expected_payload;
      new_payload_ = new_payload;
      slot_id_ = &(owner_->slot_ids[bin_][slot_]);
      special_fancy_ = false;
      assert((expected_bin_id & klockflag) == 0);
      assert((expected_slot_id & klockflag) == 0);
      just_lock_bin_ = false;
    }

    LogElt () {
    }

    void get_lock_unconditional(bool already_done) { // locks bin unconditionally
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

    // verification magic
    // false if we need to abort
    // includes built in retry mechanism for verifying records aren't in bin
    bool conditional_verify (bool already_locked, bool retry_on) { // locks if the id hasn't changed // also deals with read set
      assert(already_locked || (expected_bin_id_ & klockflag) == 0);
      assert((expected_slot_id_ & klockflag) == 0);
      assert(bin_id_ == nullptr || slot_id_ == nullptr); // we require one or the other be nullptr

      if (slot_id_ == nullptr && bin_id_ != nullptr) {
	if (already_locked) { // verifies non-existance of relavent record in bin // will return true even if had to redo reads
	  if ((expected_bin_id_ | klockflag) != *bin_id_) {
	    assert(*(bin_id_) >= expected_bin_id_);
	    // do a retry
	    uint64_t hash1 =bin_, hash2 = new_entry_, bin_id = 0;
	    if (!retry_on || owner_->find_record_ignore_bin_lock(hash1, hash2, &bin_id)) {
	      if (retry_on) cout<<"Alreadly locked case broke "<<for_write_<<endl;
	      return false; // record state of existance changed
	    }
	    // if we didn't find the record, then we just fix the write set element
	    expected_bin_id_ = bin_id;
	  }
	  return true;
	} else if (!for_write_) { // verifies non-existance of relavent record in bin
	  if (expected_bin_id_ != *bin_id_) {
	    assert(*(bin_id_) >= expected_bin_id_);
	    // do a retry
	    uint64_t hash1 =bin_, hash2 = new_entry_, bin_id = 0, slot_id = 0, slot = 0, payload = 0;
	    if (!retry_on || owner_->find_record(hash1, hash2, &bin_id, &slot_id, &slot, &payload)) {
	      if (retry_on) cout<<"Read case broke 1"<<endl;
	      return false; // record state of existance changed
	    }
	    // if we didn't find the record, then we just fix the write set element
	    expected_bin_id_ = bin_id;
	  }
	  return true;
	} else { // verifies non-existance of relavent record in bin and locks relavent bin_page
	  bool passed= false;
	  while (!passed) {
	    if (expected_bin_id_ != *bin_id_) {
	      assert(*(bin_id_) >= expected_bin_id_);
	      // do a retry
	      uint64_t hash1 =bin_, hash2 = new_entry_, bin_id = 0, slot_id = 0, slot = 0, payload = 0;
	      if (!retry_on || owner_->find_record(hash1, hash2, &bin_id, &slot_id, &slot, &payload)) {
		if (retry_on) cout<<"Write case busted"<<endl;
		return false; // record state of existance changed
	      }
	      // if we didn't find the record, then we just fix the write set element
	      expected_bin_id_ = bin_id;
	    }
	    uint64_t bin_id_guess = expected_bin_id_; // expected id has to end up unlocked so we can calculate new id correctly
	    passed = (*bin_id_).compare_exchange_weak(bin_id_guess, expected_bin_id_ | klockflag);
	  }
	  return true;
	}
      }

      if (slot_id_ != nullptr && for_write_) {
	assert(*slot_id_ == expected_slot_id_); // because we're using claim flags
	assert((*slot_id_ & kclaimflag) != 0);
	assert((*slot_id_ & klockflag) == 0);
	uint64_t slot_id_guess = expected_slot_id_;
	uint64_t t1 = *slot_id_;
	*slot_id_ = (expected_slot_id_ | klockflag);
	assert(expected_payload_ == owner_->payloads[bin_][slot_]);
	// assertion confirms that overwrites are working the way they're supposed to.
	// which is equivalent to reads working the way they're supposed to.
      }

      if (slot_id_ != nullptr && !for_write_ && ((uint64_t)(*slot_id_) | (kclaimflag)) !=
	  (expected_slot_id_ | (kclaimflag))) {
	//cout<<"Canceled"<<endl;
	return false;
      }
      return true;
    }

    void apply (uint64_t new_id) { // applies with new id which should be maximum of ids in write set
      if ((new_id & klockflag) != 0) new_id -= klockflag;
      if ((new_id & kclaimflag) != 0) new_id -= kclaimflag;
      if (for_write_) {
	assert((slot_ >= 0 || slot_ <= bin_size) && (bin_ >= 0 || bin_ < bin_num));
	uint64_t temp_id = (new_id | (klockflag));
	if (bin_id_ != nullptr) {
	  assert((*bin_id_ && klockflag) != 0);
	  assert(*bin_id_ <= temp_id); // could be equal if is second time seeing bin id in transaction
	  *bin_id_ = temp_id;
	  assert((*bin_id_ & kclaimflag) == 0);
	}
	temp_id = (new_id | (kclaimflag + klockflag));
	if (slot_id_ != nullptr) {
	  assert((*slot_id_ && klockflag) != 0);
	  assert(*slot_id_ < temp_id);
	  *slot_id_ = temp_id;
	  owner_->other_bin[bin_][slot_] = new_entry_;
	  owner_->payloads[bin_][slot_] = new_payload_;
	}
      }
    }

    void unlock (bool unlock_bin, bool kill_flag) { // unlocks
      if (for_write_) {
	if (bin_id_ != nullptr && unlock_bin) {
	  assert((*bin_id_ & klockflag) != 0);
	  *bin_id_ = *bin_id_ - klockflag;
	  if ((expected_bin_id_ | klockflag)!= 0) expected_bin_id_ -= klockflag; // may be reusing it in a second
	}
	if (slot_id_ != nullptr) {
	  assert((*slot_id_ & klockflag) != 0);
	  assert((*slot_id_ & kclaimflag) != 0);
	  *slot_id_ = *slot_id_ - klockflag;
	  if (kill_flag) *slot_id_ = *slot_id_ - kclaimflag;
	  if ((expected_slot_id_ | klockflag)!= 0) expected_slot_id_ -= klockflag; // may be reusing it in a second
	}
      }
    }

    // so we can get a global locking order // sorted by whether for write, then bin id, then slot id
    // bins before slots because when we do a retry on a bin, we don't want to deadlock with our own slot lock
    // In commit phase, need to do for writes first for serializability
    // In commit phase, in order to
    // avoid deadlock with overwrites and deletes from our own transaction during retry, we
    // unconditionally lock bin id for deletes and overwrites.
    static bool compare(const LogElt &left, const LogElt &right) {
      if (left.bin_id_ != right.bin_id_) return (left.bin_id_ > right.bin_id_); // Very important nulls go last, because retry needs to not hit deadlock with owner
      // transaction when trying to look at slots!!
      if (left.slot_id_ != right.slot_id_) return (left.slot_id_ < right.slot_id_); // want to handle bin cases before id cases to avoid deadlock with own id
      return (left.for_write_ > right.for_write_); // reads after writes
    }
  };

  // The commit protocol =============================================================
  void abort(vector <LogElt> write_set, int locked_index, bool unclaim) { // uses sorted write set

    for (uint64_t x = 0; x < locked_index; x++) {
      bool prev_bin_id_same = false;
      if (write_set[x].bin_id_ != nullptr) {
	int first_hit = x;
	while (first_hit >= 0 && write_set[first_hit].bin_id_ == write_set[x].bin_id_) first_hit--;
	first_hit++;
	if (first_hit < x && write_set[first_hit].for_write_) {
	  prev_bin_id_same = true;
	}
      }
      write_set[x].unlock(!prev_bin_id_same, unclaim);
    }
    if (unclaim) {
      for (uint64_t x = locked_index; x < write_set.size(); x++) {
	if (write_set[x].for_write_ && write_set[x].slot_id_ != nullptr) {
	  assert((*write_set[x].slot_id_ & kclaimflag) != 0);
	  (*write_set[x].slot_id_) = ((*write_set[x].slot_id_) - kclaimflag);
	  assert((*write_set[x].slot_id_ & kclaimflag) == 0);
	}
      }
    }

  }


  // aborts unsorted writeset; assumes nothing is locked, and we aborted because of claim contention for kill or increment
  void abort_unsorted_writeset(vector <LogElt> write_set, bool unclaim) { // uses unsorted write set
    if (unclaim) {
      for (uint64_t x = 0; x < write_set.size(); x++) {
	if (write_set[x].for_write_ && write_set[x].slot_id_ != nullptr) {
	  assert((*write_set[x].slot_id_ & kclaimflag) != 0);
	  (*write_set[x].slot_id_) = ((*write_set[x].slot_id_) - kclaimflag);
	  assert((*write_set[x].slot_id_ & kclaimflag) == 0);
	}
      }
    }
  }

  bool is_all_unlocked(vector <LogElt> write_set) { // only used for single thread testing!
    for (uint64_t x = 0; x < write_set.size(); x++) {
      if (write_set[x].for_write_ && slot_ids[write_set[x].bin_][write_set[x].slot_] & klockflag) return false;
      if (write_set[x].for_write_ && bin_ids[write_set[x].bin_] & klockflag) return false;
    }
    return true;
  }

  bool commit(vector <LogElt> write_set, uint64_t* worker_id) {
    // would be better to use a reference than a copy of write_set
    std::atomic_thread_fence(std::memory_order_release); // memory fence
    std::atomic_thread_fence(std::memory_order_acquire);
    bool terminate = false;
    for (uint64_t x = 0; x < write_set.size(); x++) { // just for sake of testing to make sure same record not updated twice in same transaction
      for (uint64_t y = x + 1; y < write_set.size(); y++) {
	if (write_set[x].for_write_ && write_set[y].for_write_ &&
	                            write_set[x].slot_id_ != nullptr && write_set[y].slot_id_ != nullptr &&
	    (write_set)[x].bin_ == (write_set)[y].bin_ && (write_set)[x].slot_ == (write_set)[y].slot_) {
	  terminate = true;
	}
      }
    }

    vector <LogElt> sorted_write_set (write_set.size());
    for (uint64_t x = 0; x < write_set.size(); x++) sorted_write_set[x] = write_set[x];
    std::stable_sort (sorted_write_set.begin(), sorted_write_set.end(), LogElt::compare);
    int set_size = sorted_write_set.size();

    // check write set and lock ------------------
    // lock in sorted order

    bool try_all_again = true;
    uint64_t flags = klockflag + kclaimflag;
    uint64_t new_id = *worker_id | flags;
    int repeats = 0;
    while (try_all_again) {
      repeats++;
      new_id = 0;
      try_all_again = false;
      for (uint64_t x = 0; x < write_set.size(); x++) {
	//	if (sorted_write_set[x].for_write_ || 1==1) { // By allowing read set elements through, we do a local retry for them
	// as we lock the writes. 
	  bool prev_bin_id_same = false;
	  // check if we've already locked bin
	  if (sorted_write_set[x].bin_id_ != nullptr) {
	    int first_hit = x;
	    while (first_hit >= 0 && sorted_write_set[first_hit].bin_id_ == sorted_write_set[x].bin_id_) first_hit--;
	    first_hit++; // subtracted one too much
	    if (first_hit < x && sorted_write_set[first_hit].for_write_) {
	      prev_bin_id_same = true;
	    }
	  }
	  if (!sorted_write_set[x].just_lock_bin_) {
	    if (!sorted_write_set[x].conditional_verify(prev_bin_id_same, retry_on)) {
	      // includes built in retry mechanism for bin ids // only locks if in writeset
	      // if we had a cycle in a path, this will catch it -- we're not allowed to edit the same slot twice in the same transaction
	      abort(sorted_write_set, x, true); // x tells us up to what index we need to unlock
	      return false;
	    }
	  } else {
	    sorted_write_set[x].get_lock_unconditional(prev_bin_id_same);
	  }

	  if (sorted_write_set[x].slot_id_ != nullptr) new_id = max((new_id | flags), (sorted_write_set[x].expected_slot_id_ | flags));
	  if (sorted_write_set[x].bin_id_ != nullptr) new_id = max((new_id | flags), (sorted_write_set[x].expected_bin_id_ | flags));
	  //}
      }

      std::atomic_thread_fence(std::memory_order_release); // memory fence
      std::atomic_thread_fence(std::memory_order_acquire);

      // need to verify read set // already did retries for read set a moment ago, but
      // we are willing to redo entire commit process if a read set element needs another retry
      for (uint64_t x = 0; x < write_set.size(); x++) {
	if (!sorted_write_set[x].for_write_) {
	  // check if we've already locked bin
	  if (sorted_write_set[x].bin_id_ != nullptr) {
	    bool prev_bin_id_same = false;
	    int first_hit = x;
	    while (first_hit >= 0 && sorted_write_set[first_hit].bin_id_ == sorted_write_set[x].bin_id_) first_hit--;
	    first_hit++; // subtracted one too much
	    if (first_hit < x && sorted_write_set[first_hit].for_write_) {
	      prev_bin_id_same = true;
	    }
	    bool need_retry = (sorted_write_set[x].expected_bin_id_ != *(sorted_write_set[x].bin_id_));
	    if (prev_bin_id_same == true) need_retry = ((sorted_write_set[x].expected_bin_id_ | klockflag) != (*(sorted_write_set[x].bin_id_) | klockflag));
	    if (need_retry) {
	      abort(sorted_write_set, write_set.size(), false); // unlock all
	      LogElt elt = sorted_write_set[x];
	      uint64_t hash1 = elt.bin_, hash2 = elt.new_entry_, bin_id = 0, slot_id = 0, slot = 0, payload = 0;
	      if (!retry_on || find_record(hash1, hash2, &bin_id, &slot_id, &slot, &payload)) {
		abort(sorted_write_set, 0, true); // unlock all
		if (retry_on) cout<<"Read case broke2"<<endl;
		return false; // record state of existance changed
	      }
	      // in order to retry on reads we have to unlock everything, or we risk deadlock
	      elt.expected_bin_id_ = bin_id;
	      try_all_again = true;
	      //cout<<repeats<<endl;
	      break;
	    }
	  }
	  if (sorted_write_set[x].slot_id_ != nullptr) {
	    if ((sorted_write_set[x].expected_slot_id_ | kclaimflag) !=
		(*(sorted_write_set[x].slot_id_) | kclaimflag)) {
	      abort(sorted_write_set, write_set.size(), true); // unlock all
	      return false;
	    }
	  }
	  if (sorted_write_set[x].slot_id_ != nullptr) new_id = max((new_id | flags), (sorted_write_set[x].expected_slot_id_ | flags));
	  if (sorted_write_set[x].bin_id_ != nullptr) new_id = max((new_id | flags), sorted_write_set[x].expected_bin_id_ | flags);
	}
      }
      new_id++;
      assert(!terminate);
    }

    // apply in actual order (sorted order would work also since we don't allow multiple writes to same slot)
    for (uint64_t x = 0; x < write_set.size(); x++) write_set[x].apply(new_id - klockflag);
    std::atomic_thread_fence(std::memory_order_release); // memory fence
    std::atomic_thread_fence(std::memory_order_acquire);


    // unlock in sorted order
    for (uint64_t x = 0; x < write_set.size(); x++) {
      bool prev_bin_id_same = false;
      if (sorted_write_set[x].bin_id_ != nullptr) {
	int first_hit = x;
	while (first_hit >= 0 && sorted_write_set[first_hit].bin_id_ == sorted_write_set[x].bin_id_) first_hit--;
	first_hit++;
	if (first_hit < x && sorted_write_set[first_hit].for_write_) {
	  prev_bin_id_same = true;
	}
      }
      sorted_write_set[x].unlock(!prev_bin_id_same, true);
    }
    for (uint64_t x = 0; x < write_set.size(); x++)
      if (write_set[x].for_write_ && write_set[x].slot_id_ != nullptr)
	assert(write_set[x].expected_slot_id_ < new_id);
    //assert(is_all_unlocked(write_set));
    //cout<<"Not aborted"<<endl;
    *worker_id = new_id - flags;
    return true;
  }

  // Actual hash table stuff ======================================================

  // tests for being claimed OR locked
  bool is_claimed(uint64_t num) {
    return (((num & klockflag) != 0) || ((num & kclaimflag) != 0));
  }

  bool is_locked(uint64_t num) {
    return ((num & klockflag) != 0);
  }

  bool try_to_claim(atomic <uint64_t>* num, uint64_t* final_id) {
    uint64_t expected = *num;
    if (is_claimed(expected)) return false;
    bool success = (*num).compare_exchange_weak(expected, expected | kclaimflag);
    if (success) *final_id = (expected | kclaimflag);
    return success;
  }

  // void get_claim(atomic <uint64_t>* num, uint64_t* final_id) {
  //   int attempts = 0;
  //   while (!try_to_claim(num, final_id)) {
  //     attempts++;
  //   }
  // }

  int first_empty_position(int bucket) { //First empty position if bucket is not full; -1 if bucket is full.
    for(int x=0; x<bin_size; x++) {
      if(other_bin[bucket][x]==-1 && !is_claimed(slot_ids[bucket][x])) return x;
    }
    return -1;
  }

  // Here we pick which element to kick out of the bucket
  int pick_slot(int bucket) {
    int use_empty = first_empty_position(bucket);
    if (use_empty != -1) return use_empty;
    if (cyclekick) {
      if (fancy == 0) { // Actually, is only option for fancy right now
	int answer = kickout_index[bucket];
	kickout_index[bucket]++;
	//int answer = atomic_fetch_add(&kickout_index[bucket], 1);
	return answer % bin_size;
      }
    }
    int answer = rand() % bin_size; // random walk strategy (simplest functional strategy)
    return answer;
  }

  /// Here we pick which of the two hashed to buckets to insert into. Returns one of the two choices.
  int pick_bucket(int choice1, int choice2, int *touches) {
    if (balance) return pick_bucket_balance(choice1, choice2, touches);
    // The standard way of doing it // doesn't worry about checking whether things are locked
    // because returning a bad bucket choice doesn't break anything
    *touches=*touches+1;
    if (first_empty_position(choice1) >= 0) return choice1;
    *touches=*touches+1;
    if (first_empty_position(choice2) >= 0) return choice2;
    return choice2;
  }

  int pick_bucket_balance(int choice1, int choice2, int *touches) { //Sticks in emptier of the two buckets
    *touches += 2;
    int size1=0, size2=0;
    for (int x = 0; x < bin_size; x++) {
      if (other_bin[choice1][x] != -1 && !is_claimed(slot_ids[choice1][x])) size1++;
      if (other_bin[choice2][x] != -1 && !is_claimed(slot_ids[choice2][x])) size2++;
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

  bool find_record_ignore_bin_lock(int bucket, int load, uint64_t* bin_id_chosen) {
    // used for read set retries when we locked the bin id ourselves already
    uint64_t bin_id;
    uint64_t hash1 = bucket, hash2 = load;
    uint64_t temp_payload = 0;
    bin_id = bin_ids[bucket];
    assert((bin_id & klockflag) > 0);
    *bin_id_chosen = bin_id;
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
	  return true;
	}
      }
    }
    return false;
  }

  // returns whether record was found or not.
  bool find_record(int bucket, int load, uint64_t* bin_id_chosen,
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

  int fetch_kickout_slot(int bucket) { // for system transaction kickout
    assert(bucket != -1);
    uint64_t slot = 0, slot_id = 0, temp = 0;
    bool valid_slot = false;
    while (!valid_slot) { // need to get valid slot
      slot = pick_slot(bucket);
      slot_id = slot_ids[bucket][slot];
      std::atomic_thread_fence(std::memory_order_release); // memory fence
      std::atomic_thread_fence(std::memory_order_acquire); // because we will use other bin in a second
      valid_slot = true;
      if ((slot_id & klockflag) != 0 || (slot_id & kclaimflag) != 0) valid_slot = false;
      if (other_bin[bucket][slot] == bucket) valid_slot = false;
      if (valid_slot) valid_slot = slot_ids[bucket][slot].compare_exchange_weak(slot_id, slot_id | kclaimflag);
      temp++;
      //if (temp > 100000) cout<<"Lots of waiting..."<<endl;
    }
    return slot;
  }

  void quick_lock(std::atomic <uint64_t>* id) {
    bool grabbed = false;
    uint64_t expected;
    while (!grabbed) {
      expected = *id;
      while ((expected & klockflag) != 0) expected = *id;
      // ---------------------------------------------------- SHOULD DO SOME SORT OF PAUSE IN ABOVE LOOP -------------------------------------
      grabbed = (*id).compare_exchange_weak(expected, expected | klockflag);
    }
  }

  // system transaction kickout
  // does kickout chain as system transaction
  // uses claim system to reserve kickout path, but avoids claim contention by performing kickout chain life
  // only two locks are held at a time
  // leaves first position in chain claimed for function caller to use
  bool kickout_now(uint64_t bucket, uint64_t* slot, uint64_t depth) {
    if (depth > maxchain) assert(1 == 2);
    *slot = fetch_kickout_slot(bucket); // claims for us
    if (other_bin[bucket][*slot] == -1) return true;
    uint64_t new_bin = other_bin[bucket][*slot];
    uint64_t second_slot = 0;
    kickout_now(new_bin, &second_slot, depth + 1); // recurse
    if (new_bin > bucket) { // avoid deadlock
      quick_lock(&bin_ids[new_bin]);
      quick_lock(&bin_ids[bucket]);
    } else {
      quick_lock(&bin_ids[new_bin]);
      quick_lock(&bin_ids[bucket]);
    }
    slot_ids[new_bin][second_slot] += klockflag;
    slot_ids[bucket][*slot] += klockflag;
    std::atomic_thread_fence(std::memory_order_release); // memory fence
    std::atomic_thread_fence(std::memory_order_acquire);
    payloads[new_bin][second_slot] = payloads[bucket][*slot];
    other_bin[new_bin][second_slot] = bucket;
    payloads[bucket][*slot] = 0;
    other_bin[bucket][*slot] = -1;
    uint64_t new_id = max((uint64_t)slot_ids[bucket][*slot] - kclaimflag, (uint64_t)slot_ids[new_bin][second_slot] - kclaimflag);
    new_id = max(new_id, (uint64_t)bin_ids[bucket]);
    new_id = max(new_id, (uint64_t)bin_ids[new_bin]); // new id
    assert((new_id & klockflag) != 0);
    new_id -= klockflag;
    assert((new_id & kclaimflag) == 0);
    std::atomic_thread_fence(std::memory_order_release); // memory fence
    std::atomic_thread_fence(std::memory_order_acquire);
    slot_ids[bucket][*slot] = new_id + kclaimflag; // keep claimed
    slot_ids[new_bin][second_slot] = new_id;
    bin_ids[bucket] = new_id;
    bin_ids[new_bin] = new_id;
    return true;
  }

  // insertion using live kickout chain
  int chain_live_kickout(int bucket, int other_hash, vector <LogElt>* write_set, int thread_id,
			 uint64_t payload_entry) { // Inserts -- goes down Cuckoo Chain as needed; returns length of resulting Cuckoo Chain.
    //cout<<"Insert attempt"<<endl;
    uint64_t slot_id, bin_id1 = 0, bin_id2 = 0, slot, payload = 0;
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
      if (quit1) write_set->push_back(new_entry1);
      if (quit2) write_set->push_back(new_entry2);
      return 0;
    }
    // need to verify it's not present
    LogElt entry1 = LogElt(other_hash, 0, bucket, bin_id2, 0, &bin_ids[other_hash],
			   nullptr, payload, payload, false, this); //verifying record not present
    LogElt entry2 = LogElt(bucket, 0, other_hash, bin_id1, 0, &bin_ids[bucket],
			   nullptr, payload, payload, true, this); // this one is in write set
    write_set->push_back(entry1);
    write_set->push_back(entry2);

    canceled_inserts[thread_id][1]--; // is negative the number of records added by thread
    kickout_now(bucket, &slot, 0);
    assert((slot_ids[bucket][slot] & kclaimflag) != 0);
    LogElt new_entry = LogElt(bucket, slot, other_hash, 0, slot_ids[bucket][slot],
			      0, payload_entry, true, this);
    LogElt bin_entry = new_entry;
    new_entry.bin_id_ = nullptr; // it's already in write set
    write_set->push_back(new_entry);
    return 1; // later should make return path length if I want to collect data on that
  }

  int chain(int bucket, int other_hash, int depth, vector <LogElt>* write_set, int thread_id,
	    uint64_t payload_entry) { // Inserts -- goes down Cuckoo Chain as needed; returns length of resulting Cuckoo Chain.
    if ((uint64_t) depth > maxchain) {
      cout<<"LEGIT ABORT"<<endl;
      assert(1 == 2);
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
	if (quit1) write_set->push_back(new_entry1);
	if (quit2) write_set->push_back(new_entry2);
	return 0;
      }
      // need to verify it's not present
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
      // payload is taken after slot id, so it may not be right. But if it isn't, we will abort because of the id change
      if (try_to_claim(&slot_ids[bucket][slot], &slot_id) == false) valid_slot = false;
      //      cout<<temp<<endl;
      payload = payloads[bucket][slot]; // important to do _after_ we claim (claim is atomic so gets automatic fence)
    }
    LogElt new_entry = LogElt(bucket, slot, other_hash, bin_id1, slot_id, payload,
			      payload_entry, true, this); // new payload randomly generated
    LogElt bin_entry = new_entry;
    new_entry.bin_id_ = nullptr; // it's already in write set
    bin_entry.slot_id_ = nullptr;
    bin_entry.just_lock_bin_ = true;
    if (depth > 0) write_set->push_back(bin_entry);
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

  // performs insert
  int insert(int hash1, int hash2, vector <LogElt>* write_set, int thread_id) { //returns length of Cuckoo chain used //inserts a random pair of hash functions
    //cout<<"made it to first insert"<<endl;
    int touches=0;
    int bucket = pick_bucket(hash1, hash2, &touches);
    int answer = 0;
    uint64_t new_payload = rand() % (1<<10) + 1;
    if (!live_kickout) {
      if(bucket == hash1) answer = touches + chain(bucket, hash2, 0, write_set, thread_id,
						   new_payload);
      if(bucket == hash2 && hash1 != hash2) answer = touches + chain(bucket, hash1, 0, write_set,
								     thread_id, new_payload);
    }
    if (live_kickout) {
      if(bucket == hash1) answer = touches + chain_live_kickout(bucket, hash2, write_set, thread_id,
								new_payload);
      if(bucket == hash2 && hash1 != hash2) answer = touches + chain_live_kickout(bucket, hash1, write_set,
										  thread_id, new_payload);
    }
    return answer;
  }

  // if false, need to abort entire transaction!
  bool kill(int hash1, int hash2, vector <LogElt>* write_set, int thread_id) {
    uint64_t slot_id, bin_id1 = 0, bin_id2, slot, payload = 0;
    bool tried_bin = false;
    while (!tried_bin) {
      if (find_record(hash1, hash2, &bin_id1, &slot_id, &slot, &payload)) {
	if (!is_claimed(slot_id)) {
	  bool success = (slot_ids[hash1][slot]).compare_exchange_weak(slot_id, (slot_id | kclaimflag));
	  if (success) { // if "success" failed, then we will have to check for the record again
	    LogElt entry = LogElt(hash1, slot, -1, bin_id1, slot_id, payload, 0, true, this);
	    entry.bin_id_ = nullptr;
	    write_set->push_back(entry);
	    canceled_inserts[thread_id][1]++;
	    return true;  // doesn't need to update bin id
	  }
	}
	// If you get here, then the slot was claimed, and its time to abort the entire transaction
	cout<<"kill contention abort!"<<endl;
	return false;
      } else {
	tried_bin = true;
      }
    }
    tried_bin = false;
    while (!tried_bin) {
      if (find_record(hash2, hash1, &bin_id2, &slot_id, &slot, &payload)) {
	if (!is_claimed(slot_id)) {
	  bool success = (slot_ids[hash2][slot]).compare_exchange_weak(slot_id, slot_id | kclaimflag);
	  if (success) {
	    LogElt entry = LogElt(hash2, slot, -1, bin_id2, slot_id, payload, 0, true, this);
	    //LogElt bin_entry = entry;
	    entry.bin_id_ = nullptr;
	    //bin_entry.slot_id_ = nullptr;
	    //bin_entry.just_lock_bin_ = true;
	    write_set->push_back(entry);
	    //write_set->push_back(bin_entry);
	    canceled_inserts[thread_id][1]++;
	    return true;  // doesn't need to update bin id
	  }
	}
		cout<<"kill contention abort!"<<endl;
	// If you get here, then the slot was claimed, and its time to abort the entire transaction
	return false;
      } else {
	tried_bin = true;
      }
    }
    //cout<<"Erp"<<endl;
    LogElt new_entry1 = LogElt(hash1, 0, hash2, bin_id1, 0, &bin_ids[hash1], nullptr,
			       0, 0, false, this);
    LogElt new_entry2 = LogElt(hash2, 0, hash1, bin_id2, 0, &bin_ids[hash2], nullptr,
			       0, 0 , false, this);
    write_set->push_back(new_entry1);
    write_set->push_back(new_entry2);
    return true;
  }

  // If false, need to abort entire transaction!
  // just very slightly changed kill
  bool increment_payload(int hash1, int hash2, vector <LogElt>* write_set, int thread_id) {
    uint64_t slot_id, bin_id1 = 0, bin_id2, slot, payload = 0;
    bool tried_bin = false;
    while (!tried_bin) {
      if (find_record(hash1, hash2, &bin_id1, &slot_id, &slot, &payload)) {
	if (!is_claimed(slot_id)) {
	  bool success = (slot_ids[hash1][slot]).compare_exchange_weak(slot_id, (slot_id | kclaimflag));
	  if (success) { // if "success" failed, then we will have to check for the record again
	    LogElt entry = LogElt(hash1, slot, hash2, bin_id1, slot_id, payload, payload + 1, true, this);
	    assert(is_claimed(*entry.slot_id_));
	    entry.bin_id_ = nullptr;
	    write_set->push_back(entry);
	    return true; // doesn't need to update bin id
	  }
	}
	cout<<"kill contention abort!"<<endl;
	// If you get here, then the slot was claimed, and its time to abort the entire transaction
	return false;
      } else {
	tried_bin = true;
      }
    }
    tried_bin = false;
    while (!tried_bin) {
      if (find_record(hash2, hash1, &bin_id2, &slot_id, &slot, &payload)) {
	if (!is_claimed(slot_id)) {
	  bool success = (slot_ids[hash2][slot]).compare_exchange_weak(slot_id, slot_id | kclaimflag);
	  if (success) {
	    LogElt entry = LogElt(hash2, slot, hash1, bin_id2, slot_id, payload, payload + 1, true, this);
	    entry.bin_id_ = nullptr;
	    write_set->push_back(entry);
	    return true;  // doesn't need to update bin id
	  }
	}
	cout<<"kill contention abort!"<<endl;
	// If you get here, then the slot was claimed, and its time to abort the entire transaction
	return false;
      } else {
	tried_bin = true;
      }
    }
    //cout<<"Erp"<<endl;
    LogElt new_entry1 = LogElt(hash1, 0, hash2, bin_id1, 0, &bin_ids[hash1], nullptr,
			       0, 0, false, this);
    LogElt new_entry2 = LogElt(hash2, 0, hash1, bin_id2, 0, &bin_ids[hash2], nullptr,
			       0, 0 , false, this);
    write_set->push_back(new_entry1);
    write_set->push_back(new_entry2);
    return true;
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
    //cout<<"Erp"<<endl;
    LogElt new_entry1 = LogElt(hash1, 0, hash2, bin_id1, 0, &bin_ids[hash1], nullptr,
			       0, 0, false, this);
    LogElt new_entry2 = LogElt(hash2, 0, hash1, bin_id2, 0, &bin_ids[hash2], nullptr,
			       0, 0 , false, this);
    write_set->push_back(new_entry1);
    write_set->push_back(new_entry2);
  }

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
      // is needed to put inserts last so we don't hit deadlock waiting for own claim to expire
      // Also reads have to be first because the others
      // may be dependant on the read in practice. Deletes and overwrites are the flight risks
      // -- since they are set on one record, they can hit a claim deadlock. (Insert is flexible
      // with slot choice and so doesn't face this issue). Consequently, we have to sort deletes
      // and overwrites together
    }
    Op() {
      hash1_ = -1;
      hash2_ = -1;
      operation_type_ = -1;
    }
    static bool compare(const Op &left, const Op &right) {
      if (left.operation_type_ != right.operation_type_) {
	if (left.operation_type_ * right.operation_type_ != 6) { // deletes and overwrites don't get sorted with respect to each other
	  return (left.operation_type_ < right.operation_type_);
	}
      }
      if (left.hash1_ != right.hash1_) return (left.hash1_ < right.hash1_);
      if (left.hash2_ != right.hash2_) return (left.hash2_ < right.hash2_);
      return false;
    }
  };

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

  // uses a sort order that guarantees no claim deadlocks
  void run_thread (int *pairs, int inserts, int* local_aborts, int thread_id) { // does the inserts assigned to the thread
    vector <LogElt> write_set;
    int times_tried = 0;
    int number_used = 0;
    uint64_t worker_id = 0;
    int x = 0; // bad variable name // counts position in pairs, which stores the hash pairs we get to use
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
	    //                    read(pairs[2*index], pairs[2*index + 1], &write_set, thread_id);
	    number_used++;
	  }
	}
	x++;
      }

      // build write and read sets
      //std::stable_sort (operation_set.begin(), operation_set.end(), Op::compare); //TODO: DELETE THIS AND FIX DELETES AND OVERWRITE STRATEGY TO MATCH PAPER
      bool claim_contention_abort = false;
      for (int j = 0; j < operation_set.size(); j++) {
	Op elt = operation_set[j];
	bool no_claim_contention = true;
	//cout<<thread_id<<" "<<elt.hash1_<<" "<<elt.hash2_<<" "<<elt.operation_type_<<endl;
	if (elt.operation_type_ == 1) read(elt.hash1_, elt.hash2_, &write_set, thread_id);
	if (elt.operation_type_ == 2) {
	  no_claim_contention =  kill(elt.hash1_, elt.hash2_, &write_set, thread_id);
	}
	if (elt.operation_type_ == 3) {
	  no_claim_contention = increment_payload(elt.hash1_, elt.hash2_, &write_set, thread_id);
	}
	if (elt.operation_type_ == 4) insert(elt.hash1_, elt.hash2_, &write_set, thread_id);
	if (no_claim_contention == false) {
	  claim_contention_abort = true;
	  break;
	}
      }
      
      // commit phase
      bool aborted = false;
      if (claim_contention_abort) {
	cout<<"Claim contention abort!"<<endl;
	aborted = true;
	abort_unsorted_writeset(write_set, true);
      } else {
	aborted = !commit(write_set, &worker_id);
      }
      if (aborted) { // need to retry
	//cout<<"Attempted abort"<<endl;
	if (times_tried < 20) {
	  if (times_tried == 0) *local_aborts = *local_aborts + 1;
	  //cout<<number_used<<endl;
	  //cout<<"Went with retry"<<endl;
	  x = prev_x;
	  times_tried++;
	  if (times_tried == 15) {
	    cout<<"Getting annoyed..."<<endl;
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
	assert((slot_ids[x][y] & kclaimflag) == 0);
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
    int hash_pairs [threads][inserts / threads][2];
    for (uint64_t t  = 0; t < threads; t ++) {
      for (uint64_t pair = 0; pair < inserts / threads; pair++) {
	hash_pairs[t][pair][0] = rand() % bin_num;
	hash_pairs[t][pair][1] = rand() % bin_num;
	pairs_inserted.push_back(hash_pairs[t][pair][0]);
	pairs_inserted.push_back(hash_pairs[t][pair][1]);
      }
    }

    int* aborts_table = new int[threads];
    for (uint64_t x = 0; x < threads; x++) aborts_table[x] = 0;
    vector <std::thread*> thread_array;
    /// good link: http://stackoverflow.com/questions/10673585/start-thread-with-member-function

    for (uint64_t y  = 0; y < threads; y ++) {
      thread_array.push_back(new thread(&cuckoo_table::run_thread, this, &hash_pairs[y][0][0], inserts / threads / 2, aborts_table + y, y));
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
  //srand (time(NULL)); //Initialize random seed
  srand (0); //Initialize random seed
  for(int type = only_cycle; type < 2; type++) {
    cout<<"----------"<<endl;
    vector <int> aborts(trial_num);
    double av_collisions = 0;
    for(int trial=0; trial < trial_num; trial++) {
      cuckoo_table table1;
      if (type == 0) table1.cyclekick = false;
      if (type == 1) table1.cyclekick = true;
      aborts[trial] = table1.run();
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
	<<" cycle-kick on: "<<type
	<<" kickout fancyness: "<< fancy <<endl;
    cout<<"Average aborts: "<<getav(aborts);
  }
  return 0;
}
