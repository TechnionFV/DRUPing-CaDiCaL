#ifndef _bchecker_hpp_INCLUDED
#define _bchecker_hpp_INCLUDED

#include "observer.hpp"
#include "unordered_map"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This observer implements an offline backward DRUP proof checking enabled by
// 'opts.bcheck'.

/*------------------------------------------------------------------------*/

struct BCheckerClause {
  BCheckerClause * next;
  uint64_t hash;
  unsigned size;
  Clause * unit_clause;
  int literals[1];
};

class BChecker {

  Internal * internal;

  // stack of clausal proof
  //
  vector<pair<BCheckerClause*, bool>> proof;

  // stack of clausal proof counterparts accordingly
  //
  vector<Clause*> counterparts;

  // for each counterpart 'cp', 'cp_ordering[cp]' contains all matching stack indexes
  //
  unordered_map<Clause *, vector<unsigned>> cp_ordering;
  unordered_map<int, vector<unsigned>> revive_ordering;

  void invalidate_counterpart (Clause * c, int i);
  void append_lemma (BCheckerClause* bc, Clause * c, bool deleted);

  bool inconsistent;            // found or added empty clause

  uint64_t num_clauses;         // number of clauses in hash table
  uint64_t size_clauses;        // size of clause hash table
  BCheckerClause ** clauses;    // hash table of clauses

  static const unsigned num_nonces = 4;

  uint64_t nonces[num_nonces];                      // random numbers for hashing
  uint64_t compute_hash (const vector<int> &);      // compute and save hash value of clause

  // Reduce hash value to the actual size.
  //
  static uint64_t reduce_hash (uint64_t hash, uint64_t size);

  // enlarge hash table for clauses
  //
  void enlarge_clauses ();

  BCheckerClause * new_clause (const vector<int> & lits, const uint64_t hash);
  void delete_clause (BCheckerClause *);

  // insert clause in hash table
  //
  BCheckerClause * insert (Clause *);
  BCheckerClause * insert (const vector<int> &);

  // If true, include core unit clauses.
  //
  bool core_units;

  void revive_internal_clause (int);
  void stagnate_internal_clause (const int);
  void reactivate_fixed (int);

  // popping all trail literals up to and including the literal whose antecedent is 'c'.
  //
  void undo_trail_core (Clause * c, unsigned & trail_sz);
  void undo_trail_literal (int);
  bool is_on_trail (Clause *);
  void conflict_analysis_core ();

  void mark_core (Clause *);
  void put_units_back ();

  void shrink_internal_trail (const unsigned);
  void clear ();

  void check_environment ();

  bool validate_lemma (Clause *);

  void mark_core_trail_antecedents ();


  struct {

    int64_t added;              // number of added clauses
    int64_t derived;            // number of added derived clauses
    int64_t counterparts;       // number of added counterpart references

    int64_t deleted;            // number of deleted clauses

    int64_t insertions;         // number of clauses added to hash table
    int64_t collisions;         // number of hash collisions in 'find'
    int64_t searches;           // number of searched clauses in 'find'

  } stats;

public:

  BChecker (Internal *, bool core_units = 0);
  ~BChecker ();

  void add_derived_clause (Clause *);
  void add_derived_unit_clause (const int, bool original = false);
  void add_derived_empty_clause ();

  void strengthen_clause (Clause * c, int lit);
  void flush_clause (Clause *);

  void delete_clause (const vector<int> &, bool original = false);
  void delete_clause (Clause *);

  void update_moved_counterparts ();

  bool validating;              // On during validating
  bool validate ();             // validate the clausal proof

  void print_stats ();
};

}

#endif
