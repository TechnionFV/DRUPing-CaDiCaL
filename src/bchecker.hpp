#ifndef _bchecker_hpp_INCLUDED
#define _bchecker_hpp_INCLUDED

#include "observer.hpp"
#include "unordered_map"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This observer implements an offline backward DRUP proof checking enabled by
// 'opts.bcheck'.

/*------------------------------------------------------------------------*/

class Clause;

class BCheckerClause {
public:
  unsigned revive_at;
  bool marked_garbage;
  vector<int> literals;
  BCheckerClause (vector<int> c);
  BCheckerClause (Clause * c);
  ~BCheckerClause () = default;
};

class BChecker {

  Internal * internal;

  // stack of clausal proof
  //
  vector<pair<BCheckerClause*, bool>> proof;

  // stack of clausal proof counterparts accordingly
  //
  vector<Clause*> counterparts;

  // stack containig clauses of size 1
  //
  vector<Clause *> unit_clauses;
  Clause * new_unit_clause (const int lit, bool original);


  // for each counterpart 'cp', 'cp_ordering[cp]' contains all matching stack indexes
  //
  unordered_map<Clause *, vector<unsigned>> cp_ordering;
  unordered_map<int, vector<unsigned>> revive_ordering;

  vector<int> failing_assumptions;

  void invalidate_counterpart (Clause * c, int i);
  void append_lemma (BCheckerClause* bc, Clause * c, bool deleted);

  vector<BCheckerClause *> bchecker_clauses;
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

  void mark_core (Clause *);
  void mark_last_conflict (bool);

  void shrink_internal_trail (const unsigned);
  void clear ();

  void check_environment ();

  bool validate_lemma (Clause *);
  void conflict_analysis_core ();

  void put_units_back ();
  void mark_core_trail_antecedents ();
  void reallocate ();

  bool isolate;

  struct lock_scope {
    bool & key;
    lock_scope (bool & key_) : key (key_) { assert (!key_); key = true; };
    ~lock_scope () { key = false; }
  };

  struct save_scope {
    bool & key;
    bool initial;
    save_scope (bool & key_) : key (key_) , initial (key_) {};
    ~save_scope () { key = initial; };
  };

  struct {

    int64_t added;              // number of added clauses
    int64_t derived;            // number of added derived clauses
    int64_t counterparts;       // number of added counterpart references

    int64_t deleted;            // number of deleted clauses

    int64_t insertions;         // number of clauses added to hash table

    int64_t units;              // number of searched clauses in 'find'

  } stats;

public:

  BChecker (Internal *, bool core_units = 0);
  ~BChecker ();

  void add_derived_clause (Clause *);
  void add_derived_unit_clause (const int, bool original = false);
  void add_derived_empty_clause ();

  void add_failed_assumptions (const vector<int> &);

  void strengthen_clause (Clause * c, int lit);
  void flush_clause (Clause *);

  void delete_clause (const vector<int> &, bool original = false);
  void delete_clause (Clause *);

  void update_moved_counterparts ();

  bool validating;
  bool validate (bool overconstrained = false);

  void dump_core ();

  void print_stats ();
};

}

#endif
