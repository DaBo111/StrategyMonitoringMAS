import spot
import buddy
import itertools
import os
import re
import json

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
    
    if not ap_names:
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

def load_nfa_from_json(json_file):
    import json
    with open(json_file, 'r') as f:
        data = json.load(f)
    
    bdd_dict = spot.make_bdd_dict()
    aut = spot.make_twa_graph(bdd_dict)
    
    # Map external IDs (strings/ints) to internal Spot state IDs (ints)
    id_map = {} 
    
    # 1. First Pass: Create all states
    for state_info in data['states']:
        external_id = state_info['id']
        spot_id = aut.new_state()
        id_map[external_id] = spot_id
        
    aut.set_init_state(id_map[data['initial_state']])
    
    # 2. Second Pass: Add transitions
    for state_info in data['states']:
        src_spot_id = id_map[state_info['id']]
        
        for trans in state_info.get('transitions', []):
            dst_external_id = trans['dst']
            cond_str = trans['cond']
            
            # Resolve destination ID
            if dst_external_id not in id_map:
                raise ValueError(f"Transition to unknown state: {dst_external_id}")
            dst_spot_id = id_map[dst_external_id]

            # Parse formula string to BDD
            f = spot.formula(cond_str)
            # Register APs used in this formula
            for ap in spot.atomic_prop_collect(f):
                aut.register_ap(ap)
            
            # Convert formula to BDD 
            cond_bdd = spot.formula_to_bdd(f, aut.get_dict(), aut)
            
            aut.new_edge(src_spot_id, dst_spot_id, cond_bdd)
            
    # Remap accepting states
    accepting_states = set()
    for acc_id in data.get('accepting_states', []):
        if acc_id in id_map:
            accepting_states.add(id_map[acc_id])
        else:
            print(f"Warning: Accepting state {acc_id} not found in state list.")
        
    return aut, accepting_states

def process_formula(formula_str, filename_prefix, is_negated=False):
    """
    Full pipeline: Translate -> Analyze -> Visualize
    """
    f = spot.formula(formula_str)
    if is_negated:
        f = spot.formula.Not(f)
        
    print(f"\n--- Processing Formula: {f} ---")
    
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
    
    # Example: Loading from JSON
    json_path = "nfa_example.json"
    if os.path.exists(json_path):
        print("\n" + "="*40 + "\n")
        print(f"Loading custom NFA from {json_path}...")
        custom_aut, custom_acc = load_nfa_from_json(json_path)
        print_nfa(custom_aut, custom_acc)
        save_and_visualize(custom_aut, "custom_nfa", custom_acc)

if __name__ == "__main__":
    main()
