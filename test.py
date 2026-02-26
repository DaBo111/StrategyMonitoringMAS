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
    """Create a deep copy of an automaton preserving the BDD dictionary."""
    copy = spot.make_twa_graph(aut.get_dict())
    
    for ap in aut.ap():
        copy.register_ap(ap)
    
    for _ in range(aut.num_states()):
        copy.new_state()
    
    copy.set_init_state(aut.get_init_state_number())
    
    for s in range(aut.num_states()):
        for t in aut.out(s):
            copy.new_edge(s, t.dst, t.cond)
    
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

def save_and_visualize(aut, filename, accepting_states):
    """Save automaton to DOT file and generate PNG with accepting states marked."""
    dot_content = aut.to_str('dot')
    lines = dot_content.split('\n')
    new_lines = []
    
    for line in lines:
        if 'label=' in line:
            line = line.replace('Buchi', 'NFA').replace('Büchi', 'NFA')
        
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
    
    save_and_visualize(product, filename, acc_states)


# =============================================================================
# Main
# =============================================================================

def main():
    phi_str = '(G(p | (q & (Xp))))'
    
    # Generate monitors
    neg_f = spot.formula.Not(spot.formula(phi_str))
    neg_aut = spot.translate(neg_f, 'monitor', 'det')
    print(f"Generated Monitor for Negative Case: {neg_f}")
    save_and_visualize(neg_aut, "negative_monitor", set(range(neg_aut.num_states())))

    print("\n" + "="*40 + "\n")

    f = spot.formula(phi_str)
    pos_aut = spot.translate(f, 'monitor', 'det')
    print(f"Generated Monitor for Positive Case: {f}")
    save_and_visualize(pos_aut, "positive_monitor", set(range(pos_aut.num_states())))

    # Load custom NFA
    json_path = "nfa_example.json"
    if not os.path.exists(json_path):
        print(f"\nNo custom NFA found at {json_path}")
        return
        
    print("\n" + "="*40 + "\n")
    print(f"Loading custom NFA from {json_path}...")
    
    shared_dict = pos_aut.get_dict()
    custom_aut, custom_acc = load_nfa_from_json(json_path, bdd_dict=shared_dict)
    
    print_automaton(custom_aut, custom_acc)
    save_and_visualize(custom_aut, "custom_nfa", custom_acc)

    print("\n" + "="*40 + "\n")
    
    # Compute products
    compute_and_visualize_product(
        pos_aut, "Positive", set(range(pos_aut.num_states())), 
        custom_aut, "Custom", custom_acc, 
        "product_positive_custom"
    )

    print("\n" + "="*40 + "\n")
    
    compute_and_visualize_product(
        neg_aut, "Negative", set(range(neg_aut.num_states())), 
        custom_aut, "Custom", custom_acc, 
        "product_negative_custom"
    )


if __name__ == "__main__":
    main()
