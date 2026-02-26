import spot
def print_nfa(aut, accepting):
    d = aut.get_dict()
    print("Initial:", aut.get_init_state_number())
    print("Accepting:", accepting)

    for s in range(aut.num_states()):
        print(f"\nState {s}:")
        for t in aut.out(s):
            cond = spot.bdd_format_formula(d, t.cond)
            print(f"  --[{cond}]--> {t.dst}")

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

    A_not = spot.translate(spot.formula.Not(phi), 'BA', "complete")
    A = spot.translate(phi, 'BA', "complete")

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
    bad_states_A = backward_reachable(A, accepting_states_A)

    bad_nfa = {
    "automaton": A_not,
    "accepting_states": bad_states_Anot
    }
    good_nfa = {
    "automaton": A,
    "accepting_states": bad_states_A
    }

    print("Negative NFA:")
    print_nfa(A_not, bad_states_Anot)
    print("\n\n\n")
    print("Positive NFA:")
    print_nfa(A, bad_states_A)

