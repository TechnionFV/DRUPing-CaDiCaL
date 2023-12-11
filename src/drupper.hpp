#ifndef _drupper_hpp_INCLUDED
#define _drupper_hpp_INCLUDED

#include <unordered_map>
#include <optional>
using std::optional;

namespace CaDiCaL {

/*-----------------------------------------------------------------------------------

The code implements the algorithm introduced in "DRUPing For Interpolant", a paper by
  Arie Gurfinkel and Yakir Vizel. Drupper allows DRUP-based proof trimming, validation,
  interpolants and core extraction enabled by 'opts.drup'.

Limitations:
  - Allowing other proof observers/checkers in parallel:
    During validation/trimming procedure, drupper can delete or revive clauses that
    other Internal::Proof observers aren't aware of. As a result, enabling such
    observers and checkers in parallel might trigger errors.

  - Chronological backtracking enabled by 'opts.chrono':
    The combination of chronological backtracking with the algorithm is challenging
    since invariants classically considered crucial to CDCL cease to hold.
    In its current implementation, the algorithm relies on the level order invariant
    which ensures the literals are ordered on the assignment trail in ascending order
    with respect to their decision level. This invariant is violated.
    In the interest of compatibility with chronological backtracking, adjustments to
    the implementation will be considered in the future.

  - Compatible [in/pre]processing techniques:
    1) probing / advanced probing / lookahead: not resolution based.
    2) conditioning / blocking: is this some sort of of BCE?
    3) compacting: variables are revived in the process.
    4) vivication: vivified (reason) clause must maintain first literal in its place.

  - Avoid propagating binary clauses as soon as they are marked as garbage.

-----------------------------------------------------------------------------------*/

enum DCVariant {
  CLAUSE =    0,
  LITERALS =  1
};

class DrupperClause {
  bool variant:1;
public:
  bool deleted:1;
  unsigned revive_at:30;
private:
  union {
    Clause * counterpart;
    vector<int> * literals;
  };
public:
  DrupperClause (vector<int> c, bool deletion = false, bool failing = false);
  DrupperClause (Clause * c, bool deletion = false, bool failing = false);
  ~DrupperClause ();
  DCVariant variant_type () const;
  void destroy_variant ();
  void set_variant (Clause *);
  void set_variant (const vector<int> &);
  Clause * flip_variant ();
  Clause * clause ();
  vector<int> & lits ();
  const vector<int> & lits () const;
};

struct lock_scope {
  bool & key;
  lock_scope (bool & key_) : key (key_) { assert (!key_); key = true; };
  ~lock_scope () { key = false; }
};

template<class T>
struct save_scope {
    T& key;
    T initial;
    save_scope(T& key_) : key(key_), initial(key_) { };
    save_scope(T& key_, T val_within_scope) : key(key_), initial(key_) {
      key = val_within_scope;
    };
    ~save_scope() { key = initial; };
};

class Drupper {

  Internal * internal;

  // stack of clausal proof
  //
  vector<DrupperClause *> proof;

  Clause * new_clause (const vector<int> &);
  vector<Clause *> unit_clauses;
  Clause * new_unit_clause (const int lit, bool original);

  Clause * failed_constraint;
  bool isolated;
  bool validating;
  File * file;

  bool trivially_satisfied (const vector <int> &);
  void append_lemma (DrupperClause * dc);
  void append_failed (const vector<int>  &);
  void revive_clause (int);
  void stagnate_clause (const int);
  void reactivate_fixed (int);

  void shrink_internal_trail (const unsigned);
  void clean_conflict ();

  void undo_trail_literal (const int);
  void undo_trail_core (Clause * c, unsigned & trail_sz);
  bool is_on_trail (Clause *) const;

  void mark_core (Clause *);
  void mark_conflict_lit (const int);
  void mark_conflict (bool);
  void mark_failing (const int);

  void assume_negation (const Clause *);
  bool propagate_conflict ();
  void conflict_analysis_core ();

  void mark_core_trail_antecedents ();
  void unmark_core_clauses ();
  void restore_trail ();
  void reallocate (const unsigned);
  void reconstruct (unsigned);

  void check_environment () const;
  void dump_clauses (bool active = false) const;
  void dump_clause (const Clause *) const;
  void dump_clause (const DrupperClause *) const;
  void dump_clause (const vector <int> &) const;
  void dump_proof () const;
  void dump_trail () const;

  bool core_is_unsat () const;
  void dump_core () const;
  vector<int> extract_core_literals () const;

  friend class DrupperClause;

  struct {

    int64_t solves;
    int64_t derived;            // number of added derived clauses
    int64_t deleted;            // number of deleted clauses
    int64_t revived;            // number of revived clauses
    int64_t units;              // number of unit clauses allcoated
    int64_t core;               // number of core clauses in current trim
    vector<int64_t> cores;      // number of core clauses per trim

  } stats;

  bool setup_internal_options ();

  struct Settings {

    bool core_units:1;              // mark trail reason units as core
    bool check_core:1;              // assert the set of core literals is unsat (under debug mode only)
    bool extract_core_literals:1;   // once formula have been trimmed, trim () will return core literals
    bool prefer_core:1;             // sorts watches to propagate core literals first during trim
    bool reconstruct:1;             // reconstruct the solver state after trim

    Settings () { // default
      core_units = false;
      check_core = true;
      extract_core_literals = false;
      prefer_core = false;
      reconstruct = true;
    }

  } settings;

  void save_core_phase_stats () {
    stats.cores.push_back (stats.core);
  }

public:

  Drupper (Internal *, File * f = 0);
  ~Drupper ();

  void set (const char *, bool val = true);

  void add_derived_clause (Clause *);
  void add_derived_unit_clause (const int, bool original = false);
  void add_derived_empty_clause ();
  void add_failing_assumption (const vector<int> &);
  void add_updated_clause (Clause *);

  void delete_clause (const vector<int> &, bool original = false);
  void delete_clause (Clause *);

  void deallocate_clause (Clause *);

  void update_moved_counterparts ();

  optional<vector<int>> trim (bool overconstrained = false);

  void prefer_core_watches (const int);

  void print_stats ();
};

}

#endif
