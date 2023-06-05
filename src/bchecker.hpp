#ifndef _bchecker_hpp_INCLUDED
#define _bchecker_hpp_INCLUDED

#include "observer.hpp"         // Alphabetically after 'checker'.

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This checker implements an offline backward DRUP proof checker enabled by
// 'opts.checkproofbackward' (requires 'opts.check' also to be enabled).

/*------------------------------------------------------------------------*/

struct BCheckerClause {
  BCheckerClause * next;        // collision chain link for hash table
  uint64_t hash;                // previously computed full 64-bit hash
  unsigned size;
  int literals[2];              // otherwise 'literals' of length 'size'
  bool core;
  bool garbage;
};

struct BCheckerWatch {
  int blit;
  unsigned size;
  BCheckerClause * clause;
  BCheckerWatch () { }
  BCheckerWatch (int b, BCheckerClause * c) :
    blit (b), size (c->size), clause (c)
  { }
};

typedef vector<BCheckerWatch> BCheckerWatcher;

/*------------------------------------------------------------------------*/

class BChecker : public Observer {

  Internal * internal;

  // stack of clausal proof
  //
  vector<BCheckerClause*> proof;

  // Capacity of variable values.
  //
  int64_t size_vars;

  // For the assignment we want to have an as fast access as possible and
  // thus we use an array which can also be indexed by negative literals and
  // is actually valid in the range [-size_vars+1, ..., size_vars-1].
  //
  signed char * vals;

  // The 'watchers' and 'marks' data structures are not that time critical
  // and thus we access them by first mapping a literal to 'unsigned'.
  //
  static unsigned l2u (int lit);
  vector<BCheckerWatcher> watchers;      // watchers of literals
  vector<signed char> marks;            // mark bits of literals

  signed char & mark (int lit);
  BCheckerWatcher & watcher (int lit);

  bool inconsistent;            // found or added empty clause

  uint64_t num_clauses;         // number of clauses in hash table
  uint64_t num_garbage;         // number of garbage clauses
  uint64_t size_clauses;        // size of clause hash table
  BCheckerClause ** clauses;     // hash table of clauses

  vector<int> unsimplified;     // original clause for reporting
  vector<int> simplified;       // clause for sorting

  vector<int> trail;            // for propagation

  unsigned next_to_propagate;   // next to propagate on trail

  void enlarge_vars (int64_t idx);
  void import_literal (int lit);
  void import_clause (const vector<int> &);
  bool tautological ();

  static const unsigned num_nonces = 4;

  uint64_t nonces[num_nonces];  // random numbers for hashing
  uint64_t last_hash;           // last computed hash value of clause
  uint64_t compute_hash ();     // compute and save hash value of clause

  // Reduce hash value to the actual size.
  //
  static uint64_t reduce_hash (uint64_t hash, uint64_t size);

  void enlarge_clauses ();      // enlarge hash table for clauses
  void insert ();               // insert clause in hash table
  BCheckerClause ** find ();     // find clause position in hash table

  void add_clause (const char * type);

  BCheckerClause * new_clause ();
  void delete_clause (BCheckerClause *);

  signed char val (int lit);            // returns '-1', '0' or '1'

  bool clause_satisfied (BCheckerClause*);

  void assign (int lit);        // assign a literal to true
  void assume (int lit);        // assume a literal

  struct {

    int64_t added;              // number of added clauses
    int64_t original;           // number of added original clauses
    int64_t derived;            // number of added derived clauses

    int64_t deleted;            // number of deleted clauses

    int64_t assumptions;        // number of assumed literals
    int64_t propagations;       // number of propagated literals

    int64_t insertions;         // number of clauses added to hash table
    int64_t collisions;         // number of hash collisions in 'find'
    int64_t searches;           // number of searched clauses in 'find'

    int64_t checks;             // number of implication checks

    int64_t collections;        // garbage collections
    int64_t units;

  } stats;

public:

  BChecker (Internal *);
  ~BChecker ();

  // The following three implement the 'Observer' interface.
  //
  void add_original_clause (const vector<int> &);
  void add_derived_clause (const vector<int> &);
  void delete_clause (const vector<int> &);

  bool validate ();             // validate the clausal proof

  void print_stats ();
};

}

#endif
