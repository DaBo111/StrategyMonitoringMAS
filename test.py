import spot
import buddy
import itertools
import os
import re

def get_valuation_string(cond, ap_names, ap_bdds):
    """
    Helper to expand BDD conditions into readable strings for transitions.
    """
    matching_valuations = []

    # Iterate through all 2^N combinations
    for pattern in itertools.product([True, False], repeat=len(ap_names)):
        
        # Construct the BDD for this specific valuation
        valuation_bdd = buddy.bddtrue
        valuation_str_parts = []
        
        for i, is_true in enumerate(pattern):
            if is_true:
                valuation_bdd = buddy.bdd_and(valuation_bdd, ap_bdds[i])
                valuation_str_parts.append(str(ap_names[i]))
            else:
                valuation_bdd = buddy.bdd_and(valuation_bdd, buddy.bdd_not(ap_bdds[i]))
                valuation_str_parts.append(f"!{ap_names[i]}")

        # Check if this valuation is compatible with the transition condition
        if buddy.bdd_and(cond, valuation_bdd) != buddy.bddfalse:
            matching_valuations.append(" & ".join(valuation_str_parts))
            
    return " | ".join(matching_valuations)

def print_nfa(aut, accepting_states):
    print(f"Initial: {aut.get_init_state_number()}")
    print(f"Accepting States: {accepting_states}")

    ap_names = aut.ap()
    # Pre-calculate BDD variables for APs
    ap_bdds = [buddy.bdd_ithvar(aut.register_ap(ap)) for ap in ap_names]

    # Check if there are any APs to avoid issues with empty iterators if AP set is empty
    if not ap_names:
        # Handle case with no atomic propositions if necessary,
        # otherwise the loop over product below handles the empty case correctly (1 iteration of empty tuple)
        pass

    for s in range(aut.num_states()):
        print(f"\nState {s}:")
        for t in aut.out(s):
            full_cond_str = get_valuation_string(t.cond, ap_names, ap_bdds)
            print(f"  --[{full_cond_str}]--> {t.dst}")

def compute_reverse_graph(aut):
    reverse = {s: set() for s in range(aut.num_states())}
    for s in range(aut.num_states()):
        for t in aut.out(s):
            reverse[t.dst].add(s)
    return reverse

def backward_reachable(aut, target_states):
    reverse = compute_reverse_graph(aut)
    visited = set(target_states)
    stack = list(target_states)

    while stack:
        s = stack.pop()
        for pred in reverse[s]:
            if pred not in visited:
                visited.add(pred)
                stack.append(pred)
    return visited

def get_accepting_scc_states(aut):
    """
    Identify states that belong to accepting SCCs.
    """
    scc_info = spot.scc_info(aut)
    accepting_states = set()
    for s in range(aut.num_states()):
        scc_id = scc_info.scc_of(s)
        if scc_info.is_accepting_scc(scc_id):
            accepting_states.add(s)
    return accepting_states

def save_and_visualize(aut, filename, custom_accepting_states):
    """
    Saves the automaton to a DOT file and generates a PNG.
    Modifies the DOT to visually indicate custom accepting states.
    """
    dot_content = aut.to_str('dot')
    lines = dot_content.split('\n')
    new_lines = []
    
    for line in lines:
        if 'label=' in line:
            line = line.replace('Buchi', 'NFA').replace('Büchi', 'NFA')
        
        line_stripped = line.strip()
        # Regex to match node definitions (e.g., '0 [label="..."')
        match_node = re.match(r'^(\d+)(\s|\[)', line_stripped)
        is_transition = "->" in line_stripped
        
        if match_node and not is_transition:
            state_id = int(match_node.group(1))
            if state_id in custom_accepting_states:
                if 'shape=' in line:
                    line = re.sub(r'shape=[a-z]+', 'shape=doublecircle', line)
                else:
                    # Insert shape before the closing bracket
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

def process_formula(formula_str, filename_prefix, is_negated=False):
    """
    Full pipeline: Translate -> Analyze -> Visualize
    """
    f = spot.formula(formula_str)
    if is_negated:
        f = spot.formula.Not(f)
        
    print(f"\n--- Processing: {f} ---")
    
    aut = spot.translate(f, 'BA', 'complete')
    
    if not spot.is_complete(aut):
        print(f"Warning: Automaton for {formula_str} is NOT complete")

    # 1. Identify accepting states (SCC based)
    accepting_states = get_accepting_scc_states(aut)
    
    # 2. Compute backward reachable states
    significant_states = backward_reachable(aut, accepting_states)

    # 3. Print info
    print_nfa(aut, significant_states)

    # 4. Visualize
    save_and_visualize(aut, filename_prefix, significant_states)
    
    return aut, significant_states

def main():
    phi_str = '(G(p | (q & (Xp))))'
    
    # Process Negative Case
    process_formula(phi_str, "negative_nfa", is_negated=True)
    
    print("\n" + "="*40 + "\n")

    # Process Positive Case
    process_formula(phi_str, "positive_nfa", is_negated=False)

if __name__ == "__main__":
    main()