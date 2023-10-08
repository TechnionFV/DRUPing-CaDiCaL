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
  bool failed;
  int revive_at;
  bool marked_garbage;
  vector<int> literals;
  BCheckerClause (vector<int> c);
  BCheckerClause (Clause * c);
  ~BCheckerClause () = default;
  bool unit () const {
    return literals.size () == 1;
  }
};

class BChecker {

  Internal * internal;

  // stack of clausal proof
  //
  vector<pair<BCheckerClause*, bool>> proof;

  // stack of clausal proof internal counterparts accordingly
  //
  vector<Clause*> counterparts;

  // stack containig clauses of size 1
  //
  vector<Clause *> unit_clauses;
  Clause * new_unit_clause (const int lit, bool original);

  // for each counterpart 'cp', 'cp_ordering[cp]' contains matching stack index
  //
  unordered_map<Clause *, vector<unsigned>> cp_ordering;

  bool core_units;
  bool isolate;
  bool validating;

  vector<BCheckerClause *> bchecker_clauses;
  BCheckerClause * insert (Clause *);
  BCheckerClause * insert (const vector<int> &);

  void append_lemma (BCheckerClause* bc, Clause * c, bool deleted);
  void revive_internal_clause (int);
  void stagnate_internal_clause (const int);
  void reactivate_fixed (int);

  void shrink_internal_trail (const unsigned);
  void clear_conflict ();

  // popping all trail literals up to and including the literal whose antecedent is 'c'.
  //
  void undo_trail_literal (int);
  void undo_trail_core (Clause * c, unsigned & trail_sz);
  bool is_on_trail (Clause *);

  void mark_core (Clause *);
  void mark_conflict_lit (int l);
  void mark_conflict (bool overconstarined);

  void assume_negation (const Clause *);
  bool propagate_conflict ();
  void conflict_analysis_core ();

  void mark_core_trail_antecedents ();
  void reallocate ();
  void put_units_back ();
  void pop_failing_assumptions (unsigned);


  // debugging only
  //
  void check_environment ();
  void dump_proof ();
  void dump_core ();

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

    int64_t derived;            // number of added derived clauses
    int64_t deleted;            // number of deleted clauses
    int64_t counterparts;       // number of counterpart references
    int64_t units;              // number of unit clauses allcoated
    int64_t core;               // number of unit clauses allcoated

  } stats;

public:

  BChecker (Internal *, bool core_units = 0);
  ~BChecker ();

  void add_derived_clause (Clause *);
  void add_derived_unit_clause (const int, bool original = false);
  void add_derived_empty_clause ();

  void add_failing_assumption (const vector<int> &);

  void strengthen_clause (Clause * c, int lit);
  void flush_clause (Clause *);

  void delete_clause (const vector<int> &, bool original = false);
  void delete_clause (Clause *);

  void update_moved_counterparts ();

  bool validate (bool overconstrained = false);

  void print_stats ();
};

}

#endif
