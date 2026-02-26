import spot
import buddy

def print_nfa(aut, accepting):
    d = aut.get_dict()
    print("Initial:", aut.get_init_state_number())
    print("Accepting:", accepting)

    ap_bdds = []
    ap_names = []
    for ap in aut.ap():
        ap_names.append(ap)
        # We need the BDD variable corresponding to the atomic proposition
        v = aut.register_ap(ap)
        ap_bdds.append(buddy.bdd_ithvar(v))

    import itertools

    for s in range(aut.num_states()):
        print(f"\nState {s}:")
        for t in aut.out(s):
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
                # i.e., (TransCond AND Valuation) != False
                if buddy.bdd_and(t.cond, valuation_bdd) != buddy.bddfalse:
                    matching_valuations.append(" & ".join(valuation_str_parts))
            
            # Print the expanded conditions
            full_cond_str = " | ".join(matching_valuations)
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
if __name__ == "__main__":
    phi = spot.formula('(G(p | (q & (Xp))))')

    A_not = spot.translate(spot.formula.Not(phi), 'BA', 'complete')
    if not spot.is_complete(A_not):
        print("Warning: A_not is NOT complete")
    
    A = spot.translate(phi, 'BA', 'complete')
    if not spot.is_complete(A):
        print("Warning: A is NOT complete")

    scc_Anot = spot.scc_info(A_not)
    accepting_states_Anot = set()

    scc_A = spot.scc_info(A)
    accepting_states_A = set()

    for s in range(A_not.num_states()):
        scc_id = scc_Anot.scc_of(s)
        if scc_Anot.is_accepting_scc(scc_id):
            accepting_states_Anot.add(s)

    for s in range(A.num_states()):
        scc_id = scc_A.scc_of(s)
        if scc_A.is_accepting_scc(scc_id):
            accepting_states_A.add(s)

    bad_states_Anot = backward_reachable(A_not, accepting_states_Anot)
    good_states_A = backward_reachable(A, accepting_states_A)

    bad_nfa = {
    "automaton": A_not,
    "accepting_states": bad_states_Anot
    }
    good_nfa = {
    "automaton": A,
    "accepting_states": good_states_A
    }

    print("Negative NFA:")
    print_nfa(A_not, bad_states_Anot)
    print("\n\n\n")
    print("Positive NFA:")
    print_nfa(A, good_states_A)

    # Visualization
    def save_and_visualize(aut, filename, custom_accepting_states):
        import re
        import os
        
        # 1. Get the raw DOT string from spot
        dot_content = aut.to_str('dot')
        
        lines = dot_content.split('\n')
        new_lines = []
        for line in lines:
            line_stripped = line.strip()
            # Simple heuristic: node lines start with a digit and do not contain '->'
            # e.g., '0 [label="0", ...]'
            # Transition lines contain '->' e.g., '0 -> 1 [label="..."]'
            
            # Use regex to find lines that start with a number followed by space or [
            match_node = re.match(r'^(\d+)(\s|\[)', line_stripped)
            is_transition = "->" in line_stripped
            
            if match_node and not is_transition:
                state_id = int(match_node.group(1))
                if state_id in custom_accepting_states:
                    # It's one of our accepting states, make it doublecircle
                    if 'shape=' in line:
                        line = re.sub(r'shape=[a-z]+', 'shape=doublecircle', line)
                    else:
                        # Insert shape inside the brackets.
                        # Usually line ends with ] or ];
                        # Find the last ]
                        idx = line.rfind(']')
                        if idx != -1:
                            line = line[:idx] + ', shape=doublecircle' + line[idx:]
            new_lines.append(line)
        
        updated_dot = "\n".join(new_lines)
        
        with open(f"{filename}.dot", "w") as f:
            f.write(updated_dot)
        print(f"Saved DOT file: {filename}.dot")
        
        # Try to run dot to generate png
        try:
            ret = os.system(f"dot -Tpng {filename}.dot -o {filename}.png")
            if ret == 0:
                print(f"Generated {filename}.png")
            else:
                print(f"Warning: 'dot' command returned error code {ret}. PNG not generated.")
        except Exception as e:
            print(f"Could not run dot: {e}")

    print("\nGenerating visualizations...")
    save_and_visualize(A_not, "negative_nfa", bad_states_Anot)
    save_and_visualize(A, "positive_nfa", good_states_A)

