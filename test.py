"""
Finite-word automata operations using Spot library.
Supports NFA construction, completion, product computation, and visualization.
"""

import spot
import buddy
import itertools
import os
import re
import json


# =============================================================================
# BDD / Transition Utilities
# =============================================================================

def get_valuation_string(cond, ap_names, ap_bdds):
    """Expand BDD condition into readable string for transitions."""
    matching_valuations = []

    for pattern in itertools.product([True, False], repeat=len(ap_names)):
        valuation_bdd = buddy.bddtrue
        valuation_str_parts = []
        
        for i, is_true in enumerate(pattern):
            if is_true:
                valuation_bdd = buddy.bdd_and(valuation_bdd, ap_bdds[i])
                valuation_str_parts.append(str(ap_names[i]))
            else:
                valuation_bdd = buddy.bdd_and(valuation_bdd, buddy.bdd_not(ap_bdds[i]))
                valuation_str_parts.append(f"!{ap_names[i]}")

        if buddy.bdd_and(cond, valuation_bdd) != buddy.bddfalse:
            matching_valuations.append(" & ".join(valuation_str_parts))
            
    return " | ".join(matching_valuations)


# =============================================================================
# Automaton Utilities
# =============================================================================

def print_automaton(aut, accepting_states):
    """Print automaton structure to stdout."""
    print(f"Initial: {aut.get_init_state_number()}")
    print(f"Accepting States: {accepting_states}")

    ap_names = aut.ap()
    ap_bdds = [buddy.bdd_ithvar(aut.register_ap(ap)) for ap in ap_names]

    for s in range(aut.num_states()):
        print(f"\nState {s}:")
        for t in aut.out(s):
            cond_str = get_valuation_string(t.cond, ap_names, ap_bdds)
            print(f"  --[{cond_str}]--> {t.dst}")


def copy_automaton(aut):
    """Create a deep copy of an automaton preserving the BDD dictionary and acceptance."""
    copy = spot.make_twa_graph(aut.get_dict())
    
    # Copy atomic propositions
    for ap in aut.ap():
        copy.register_ap(ap)
    
    # Copy states
    for _ in range(aut.num_states()):
        copy.new_state()
    
    copy.set_init_state(aut.get_init_state_number())
    
    # Copy acceptance condition
    copy.copy_acceptance_of(aut)
    
    # Copy edges WITH acceptance marks
    for s in range(aut.num_states()):
        for t in aut.out(s):
            copy.new_edge(s, t.dst, t.cond, t.acc)
    
    return copy


def set_finite_acceptance(aut):
    """
    Configure automaton for finite-word semantics.
    Clears edge acceptance marks (state-based acceptance tracked externally).
    """
    aut.set_acceptance(0, spot.acc_code("t"))
    for e in aut.edges():
        e.acc = spot.mark_t([])


def is_complete(aut):
    """Check if automaton is complete (total): every state covers all valuations."""
    for s in range(aut.num_states()):
        total_cond = buddy.bddfalse
        for t in aut.out(s):
            total_cond = buddy.bdd_or(total_cond, t.cond)
        
        if total_cond != buddy.bddtrue:
            return False
    return True


def complete_automaton(aut, accepting_states):
    """
    Make automaton complete by adding a non-accepting sink state.
    Returns (automaton, accepting_states) - automaton is modified in place.
    """
    if is_complete(aut):
        return aut, accepting_states
    
    sink = aut.new_state()
    aut.new_edge(sink, sink, buddy.bddtrue)
    
    for s in range(aut.num_states()):
        if s == sink:
            continue
        
        covered = buddy.bddfalse
        for t in aut.out(s):
            covered = buddy.bdd_or(covered, t.cond)
        
        missing = buddy.bdd_not(covered)
        if missing != buddy.bddfalse:
            aut.new_edge(s, sink, missing)
    
    return aut, accepting_states


# =============================================================================
# Visualization
# =============================================================================

def save_and_visualize(aut, filename, accepting_states, label=None):
    """Save automaton to DOT file and generate PNG with accepting states marked."""
    dot_content = aut.to_str('dot')
    lines = dot_content.split('\n')
    new_lines = []
    
    for line in lines:
        # Replace the graph label (not state labels or edge labels)
        # Graph label appears early in the DOT file and starts with just "label="
        if label and line.strip().startswith('label=') and 'labelloc=' not in line:
            # This is the graph label line - replace with custom label
            line = re.sub(r'label="[^"]*"', f'label="{label}"', line)
        
        line_stripped = line.strip()
        match_node = re.match(r'^(\d+)(\s|\[)', line_stripped)
        is_transition = "->" in line_stripped
        
        if match_node and not is_transition:
            state_id = int(match_node.group(1))
            if state_id in accepting_states:
                if 'shape=' in line:
                    line = re.sub(r'shape=[a-z]+', 'shape=doublecircle', line)
                else:
                    idx = line.rfind(']')
                    if idx != -1:
                        line = line[:idx] + ', shape=doublecircle' + line[idx:]
        new_lines.append(line)
    
    updated_dot = "\n".join(new_lines)
    dot_path = f"{filename}.dot"
    png_path = f"{filename}.png"

    with open(dot_path, "w") as f:
        f.write(updated_dot)
    print(f"Saved DOT: {dot_path}")
    
    try:
        ret = os.system(f"dot -Tpng {dot_path} -o {png_path}")
        if ret == 0:
            print(f"Generated PNG: {png_path}")
        else:
            print(f"Warning: 'dot' command failed (code {ret}).")
    except Exception as e:
        print(f"Could not run dot: {e}")


# =============================================================================
# JSON Loading
# =============================================================================

def load_kripke_as_buchi(json_file, bdd_dict=None):
    """
    Load Kripke structure from JSON and interpret as Buchi automaton.
    
    In Kripke structures, atomic propositions label states (not transitions).
    When converting to Buchi automaton:
    - Transitions are labeled with the source state's atomic propositions
    - All states are accepting (standard for Kripke structure semantics)
    
    JSON format:
    {
      "ap": ["p", "q", ...],
      "initial_state": "s0",
      "states": [
        {
          "id": "s0",
          "labels": ["p"],        // atomic propositions true in this state
          "successors": ["s1"]    // outgoing edges (state IDs)
        },
        ...
      ]
    }
    
    Args:
        json_file: Path to JSON file containing Kripke structure
        bdd_dict: Optional BDD dictionary to share with other automata
        
    Returns:
        (automaton, accepting_states) where all states are accepting
    """
    with open(json_file, 'r') as f:
        data = json.load(f)
    
    if bdd_dict is None:
        bdd_dict = spot.make_bdd_dict()
        
    aut = spot.make_twa_graph(bdd_dict)
    
    # Register all atomic propositions
    all_aps = data.get('ap', [])
    ap_bdds = {}
    for ap_name in all_aps:
        aut.register_ap(ap_name)
        ap_bdds[ap_name] = buddy.bdd_ithvar(aut.register_ap(ap_name))
    
    # Create states and build ID mapping
    id_map = {}
    state_labels = {}
    
    for state_info in data['states']:
        external_id = state_info['id']
        spot_id = aut.new_state()
        id_map[external_id] = spot_id
        state_labels[spot_id] = state_info.get('labels', [])
    
    # Set initial state
    aut.set_init_state(id_map[data['initial_state']])
    
    # Add transitions with labels based on source state
    for state_info in data['states']:
        src_id = state_info['id']
        src = id_map[src_id]
        src_labels = state_labels[src]
        
        # Build BDD for source state labels
        # Conjunction of all labels true at source and negation of others
        label_bdd = buddy.bddtrue
        for ap_name in all_aps:
            if ap_name in src_labels:
                label_bdd = buddy.bdd_and(label_bdd, ap_bdds[ap_name])
            else:
                label_bdd = buddy.bdd_and(label_bdd, buddy.bdd_not(ap_bdds[ap_name]))
        
        # Add edge to each successor with the source state's label
        for dst_id in state_info.get('successors', []):
            if dst_id not in id_map:
                raise ValueError(f"Transition to unknown state: {dst_id}")
            dst = id_map[dst_id]
            aut.new_edge(src, dst, label_bdd)
    
    # All states are accepting in Buchi interpretation of Kripke structure
    accepting_states = set(range(aut.num_states()))
    
    # Set Buchi acceptance
    # For Kripke structures, all infinite runs are accepting
    # Use generalized Buchi acceptance: Inf(0) with all edges marked
    aut.set_acceptance(1, spot.acc_code("Inf(0)"))
    for e in aut.edges():
        e.acc = spot.mark_t([0])
    
    return aut, accepting_states


def load_nfa_from_json(json_file, bdd_dict=None):
    """
    Load NFA from JSON file.
    
    Args:
        json_file: Path to JSON file
        bdd_dict: Optional BDD dictionary to share with other automata
        
    Returns:
        (automaton, accepting_states)
    """
    with open(json_file, 'r') as f:
        data = json.load(f)
    
    if bdd_dict is None:
        bdd_dict = spot.make_bdd_dict()
        
    aut = spot.make_twa_graph(bdd_dict)
    id_map = {}
    
    # Create states
    for state_info in data['states']:
        external_id = state_info['id']
        spot_id = aut.new_state()
        id_map[external_id] = spot_id
        
    aut.set_init_state(id_map[data['initial_state']])
    
    # Add transitions
    for state_info in data['states']:
        src = id_map[state_info['id']]
        
        for trans in state_info.get('transitions', []):
            dst_id = trans['dst']
            if dst_id not in id_map:
                raise ValueError(f"Transition to unknown state: {dst_id}")
            
            dst = id_map[dst_id]
            f = spot.formula(trans['cond'])
            
            for ap in spot.atomic_prop_collect(f):
                aut.register_ap(ap)
            
            cond_bdd = spot.formula_to_bdd(f, aut.get_dict(), aut)
            aut.new_edge(src, dst, cond_bdd)
            
    # Map accepting states
    accepting_states = set()
    for acc_id in data.get('accepting_states', []):
        if acc_id in id_map:
            accepting_states.add(id_map[acc_id])
        else:
            print(f"Warning: Accepting state {acc_id} not found.")

    set_finite_acceptance(aut)
    return aut, accepting_states


# =============================================================================
# Product Construction
# =============================================================================

def compute_product(aut1, aut2):
    """
    Compute product automaton with state-pair tracking.
    
    Returns:
        (product_automaton, state_pairs) where state_pairs maps 
        product state ID -> (s1, s2)
    """
    product = spot.make_twa_graph(aut1.get_dict())
    
    for ap in aut1.ap():
        product.register_ap(ap)
    for ap in aut2.ap():
        product.register_ap(ap)
    
    pair_to_pid = {}
    state_pairs = {}
    
    def get_or_create_state(s1, s2):
        if (s1, s2) not in pair_to_pid:
            pid = product.new_state()
            pair_to_pid[(s1, s2)] = pid
            state_pairs[pid] = (s1, s2)
        return pair_to_pid[(s1, s2)]
    
    init1 = aut1.get_init_state_number()
    init2 = aut2.get_init_state_number()
    init_pid = get_or_create_state(init1, init2)
    product.set_init_state(init_pid)
    
    # BFS exploration
    queue = [(init1, init2)]
    visited = {(init1, init2)}
    
    while queue:
        s1, s2 = queue.pop(0)
        src_pid = pair_to_pid[(s1, s2)]
        
        for t1 in aut1.out(s1):
            for t2 in aut2.out(s2):
                cond = buddy.bdd_and(t1.cond, t2.cond)
                if cond == buddy.bddfalse:
                    continue
                
                dst1, dst2 = t1.dst, t2.dst
                dst_pid = get_or_create_state(dst1, dst2)
                product.new_edge(src_pid, dst_pid, cond)
                
                if (dst1, dst2) not in visited:
                    visited.add((dst1, dst2))
                    queue.append((dst1, dst2))
    
    return product, state_pairs


def compute_product_accepting_states(state_pairs, acc1, acc2):
    """Compute accepting states for product: intersection of acceptance."""
    return {pid for pid, (s1, s2) in state_pairs.items() 
            if s1 in acc1 and s2 in acc2}


def compute_and_visualize_product(aut1, name1, acc1, aut2, name2, acc2, filename):
    """
    Compute product of two finite-word automata and visualize.
    
    - Completes automata if needed (on copies)
    - Uses state-based intersection for acceptance
    - Verifies product totality
    """
    print(f"Computing product: {name1} x {name2}")

    aut1_complete = is_complete(aut1)
    aut2_complete = is_complete(aut2)
    print(f"  {name1} automaton is complete: {aut1_complete}")
    print(f"  {name2} automaton is complete: {aut2_complete}")
    
    # Work on copies to preserve originals
    aut1_copy = copy_automaton(aut1)
    aut2_copy = copy_automaton(aut2)
    acc1_copy = set(acc1)
    acc2_copy = set(acc2)
    
    if not aut1_complete:
        print(f"  Completing {name1} automaton...")
        aut1_copy, acc1_copy = complete_automaton(aut1_copy, acc1_copy)
    if not aut2_complete:
        print(f"  Completing {name2} automaton...")
        aut2_copy, acc2_copy = complete_automaton(aut2_copy, acc2_copy)

    set_finite_acceptance(aut1_copy)
    set_finite_acceptance(aut2_copy)

    try:
        product, state_pairs = compute_product(aut1_copy, aut2_copy)
    except Exception as e:
        print(f"Error computing product: {e}")
        return

    print(f"Product has {product.num_states()} states.")
    
    acc_states = compute_product_accepting_states(state_pairs, acc1_copy, acc2_copy)
    print(f"Computed Intersection Accepting States: {acc_states}")
    
    set_finite_acceptance(product)
    
    print(f"Product automaton is complete: {is_complete(product)}")
    
    save_and_visualize(product, filename, acc_states, f"{name1} × {name2} NFA Product")


def compute_and_visualize_buchi_product(aut1, name1, aut2, name2, filename):
    """
    Compute product of two Buchi automata and visualize.
    
    Uses Spot's built-in product which properly handles Buchi acceptance.
    For Buchi automata with Inf(0) acceptance, the product has acceptance
    condition that ensures both automata accept (intersection semantics).
    
    Args:
        aut1, aut2: Buchi automata to compute product of
        name1, name2: Names for logging
        filename: Output filename for visualization
    """
    print(f"Computing Buchi product: {name1} x {name2}")
    print(f"  {name1} has {aut1.num_states()} states")
    print(f"  {name2} has {aut2.num_states()} states")
    
    # Use Spot's built-in product for Buchi automata
    product = spot.product(aut1, aut2)
    
    print(f"Product has {product.num_states()} states.")
    print(f"Product acceptance: {product.get_acceptance()}")
    
    # Extract accepting states from product for visualization
    # For Buchi automata, a state is "accepting" if it has outgoing edges with acceptance marks
    accepting_states = set()
    for s in range(product.num_states()):
        for e in product.out(s):
            # Check if the edge has non-empty acceptance marks
            if e.acc != spot.mark_t([]):
                accepting_states.add(s)
                break
    
    print(f"States with accepting transitions: {accepting_states}")
    
    save_and_visualize(product, filename, accepting_states, f"{name1} × {name2} Buchi Product")
    
    return product, accepting_states


def buchi_to_prefix_nfa(buchi_aut, name="automaton"):
    """
    Convert Buchi automaton to prefix NFA (finite-word automaton).
    
    Algorithm:
    1. Compute all SCCs in the Buchi automaton
    2. Identify accepting SCCs (contain at least one accepting edge)
    3. Mark states as accepting if they can reach an accepting SCC
    
    Args:
        buchi_aut: Buchi automaton to convert
        name: Name for logging
        
    Returns:
        (prefix_nfa, accepting_states)
    """
    print(f"Converting {name} to prefix NFA...")
    
    # Step 1: Compute SCCs on the original Buchi automaton
    sccs = compute_sccs(buchi_aut)
    print(f"  Found {len(sccs)} SCCs: {sccs}")
    
    # Step 2: Identify accepting SCCs (contain at least one accepting edge)
    accepting_sccs = set()
    for scc_id, scc_states in enumerate(sccs):
        if is_scc_accepting(buchi_aut, scc_states):
            accepting_sccs.add(scc_id)
            print(f"    SCC {scc_id} {scc_states} is accepting")
    
    print(f"  {len(accepting_sccs)} accepting SCCs")
    
    # Step 3: Find all states that can reach an accepting SCC
    accepting_states = set()
    for s in range(buchi_aut.num_states()):
        for scc_id in accepting_sccs:
            if can_reach_scc(buchi_aut, s, sccs[scc_id]):
                accepting_states.add(s)
                break
    
    print(f"  Prefix NFA has {len(accepting_states)} accepting states: {accepting_states}")
    
    # Create the prefix NFA with same structure but finite-word acceptance
    prefix_nfa = copy_automaton(buchi_aut)
    set_finite_acceptance(prefix_nfa)
    
    return prefix_nfa, accepting_states


def compute_sccs(aut):
    """
    Compute strongly connected components using Tarjan's algorithm.
    Returns list of SCCs, where each SCC is a set of state IDs.
    """
    index_counter = [0]
    stack = []
    lowlinks = {}
    index = {}
    on_stack = {}
    sccs = []
    
    def strongconnect(v):
        index[v] = index_counter[0]
        lowlinks[v] = index_counter[0]
        index_counter[0] += 1
        on_stack[v] = True
        stack.append(v)
        
        for e in aut.out(v):
            w = e.dst
            if w not in index:
                strongconnect(w)
                lowlinks[v] = min(lowlinks[v], lowlinks[w])
            elif on_stack.get(w, False):
                lowlinks[v] = min(lowlinks[v], index[w])
        
        if lowlinks[v] == index[v]:
            scc = set()
            while True:
                w = stack.pop()
                on_stack[w] = False
                scc.add(w)
                if w == v:
                    break
            sccs.append(scc)
    
    for v in range(aut.num_states()):
        if v not in index:
            strongconnect(v)
    
    return sccs


def is_scc_accepting(aut, scc_states):
    """
    Check if an SCC contains at least one accepting edge.
    An SCC is accepting if there's an edge within the SCC with acceptance marks.
    """
    for s in scc_states:
        for e in aut.out(s):
            # Edge must stay within the SCC and have acceptance marks
            if e.dst in scc_states and e.acc != spot.mark_t([]):
                return True
    return False


def can_reach_scc(aut, start, target_scc):
    """
    Check if there's a path from start state to any state in target_scc.
    """
    if start in target_scc:
        return True
    
    visited = set([start])
    queue = [start]
    
    while queue:
        current = queue.pop(0)
        
        for e in aut.out(current):
            if e.dst in target_scc:
                return True
            
            if e.dst not in visited:
                visited.add(e.dst)
                queue.append(e.dst)
    
    return False


def get_buchi_accepting_states(aut):
    """
    Extract accepting states from a Buchi automaton.
    For Buchi automata, states with outgoing edges marked with acceptance
    sets are considered accepting for visualization purposes.
    """
    accepting_states = set()
    for s in range(aut.num_states()):
        for e in aut.out(s):
            if e.acc != spot.mark_t([]):
                accepting_states.add(s)
                break
    return accepting_states


# =============================================================================
# Main
# =============================================================================

def main():
    phi_str = '(G(p | (q & (Xp))))'
    
    # Generate Buchi automata
    # Use 'complete' option to add explicit rejecting sink states
    neg_f = spot.formula.Not(spot.formula(phi_str))
    neg_aut = spot.translate(neg_f, 'Buchi', 'complete')
    print(f"Generated Buchi Automaton for Negative Case: {neg_f}")
    print(f"  Acceptance condition: {neg_aut.get_acceptance()}")
    print(f"  Num states: {neg_aut.num_states()}")
    neg_acc = get_buchi_accepting_states(neg_aut)
    save_and_visualize(neg_aut, "negative_buchi", neg_acc, f"Negative Buchi: {neg_f}")

    print("\n" + "="*40 + "\n")

    f = spot.formula(phi_str)
    # Translate to Buchi automaton with completion
    pos_aut_incomplete = spot.translate(f, 'Buchi', 'complete')
    print(f"Generated Buchi Automaton for Positive Case: {f}")
    print(f"  Acceptance condition: {pos_aut_incomplete.get_acceptance()}")
    print(f"  Num states: {pos_aut_incomplete.num_states()}")
    
    # Debug: print which edges have acceptance marks
    print(f"  Edge acceptance marks:")
    for s in range(pos_aut_incomplete.num_states()):
        for e in pos_aut_incomplete.out(s):
            print(f"    State {s} -> {e.dst}: acc={e.acc}")
    
    pos_acc = get_buchi_accepting_states(pos_aut_incomplete)
    print(f"  States with accepting edges: {pos_acc}")
    
    # Check if automaton is complete
    print(f"  Automaton is complete: {is_complete(pos_aut_incomplete)}")
    
    pos_aut = pos_aut_incomplete
    save_and_visualize(pos_aut, "positive_buchi", pos_acc, f"Positive Buchi: {f}")

    # Convert standalone Buchi automata to prefix NFAs
    print("\n" + "="*40 + "\n")
    neg_prefix_standalone, neg_prefix_standalone_acc = buchi_to_prefix_nfa(neg_aut, "Negative Buchi")
    save_and_visualize(neg_prefix_standalone, "negative_prefix_nfa", neg_prefix_standalone_acc, f"Negative Prefix NFA: {neg_f}")

    print("\n" + "="*40 + "\n")
    pos_prefix_standalone, pos_prefix_standalone_acc = buchi_to_prefix_nfa(pos_aut, "Positive Buchi")
    save_and_visualize(pos_prefix_standalone, "positive_prefix_nfa", pos_prefix_standalone_acc, f"Positive Prefix NFA: {f}")

    # Load Kripke structure as Buchi automaton
    kripke_path = "kripke_example.json"
    if not os.path.exists(kripke_path):
        print(f"\nNo Kripke structure found at {kripke_path}")
        return
        
    print("\n" + "="*40 + "\n")
    print(f"Loading Kripke structure from {kripke_path}...")
    
    shared_dict = pos_aut.get_dict()
    kripke_aut, kripke_acc = load_kripke_as_buchi(kripke_path, bdd_dict=shared_dict)
    
    print_automaton(kripke_aut, kripke_acc)
    save_and_visualize(kripke_aut, "kripke_as_buchi", kripke_acc, "Kripke Structure (Buchi)")

    print("\n" + "="*40 + "\n")
    
    # Compute product with positive Buchi automaton
    pos_product, _ = compute_and_visualize_buchi_product(
        pos_aut, "Positive", 
        kripke_aut, "Kripke", 
        "product_positive_buchi"
    )
    
    # Convert to prefix NFA
    print("\n" + "="*40 + "\n")
    pos_prefix_nfa, pos_prefix_acc = buchi_to_prefix_nfa(pos_product, "Positive Product")
    save_and_visualize(pos_prefix_nfa, "prefix_product_nfa_positive", pos_prefix_acc, f"Positive Product Prefix NFA: ({f}) ∩ Kripke")

    print("\n" + "="*40 + "\n")
    
    # Compute product with negative Buchi automaton
    neg_product, _ = compute_and_visualize_buchi_product(
        neg_aut, "Negative", 
        kripke_aut, "Kripke", 
        "product_negative_buchi"
    )
    
    # Convert to prefix NFA
    print("\n" + "="*40 + "\n")
    neg_prefix_nfa, neg_prefix_acc = buchi_to_prefix_nfa(neg_product, "Negative Product")
    save_and_visualize(neg_prefix_nfa, "prefix__product_nfa_negative", neg_prefix_acc, f"Negative Product Prefix NFA: ({neg_f}) ∩ Kripke")


if __name__ == "__main__":
    main()
