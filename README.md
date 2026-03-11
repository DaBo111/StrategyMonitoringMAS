# LTL Model Checking with Buchi Automata

This tool performs LTL model checking by:
1. Converting LTL formulas to Buchi automata
2. Loading Kripke structures and interpreting them as Buchi automata
3. Computing products of Buchi automata
4. Converting Buchi automata to prefix NFAs (finite-word automata)

## Workflow

The script (`test.py`) performs the following operations:

1. **Generate Buchi Automata**: Translates LTL formulas φ and ¬φ to complete Buchi automata
2. **Convert to Prefix NFAs**: Generates standalone prefix NFAs from the Buchi automata
3. **Load Kripke Structure**: Reads a Kripke structure from JSON and interprets it as a Buchi automaton
4. **Compute Products**: Creates Buchi products of (Positive × Kripke) and (Negative × Kripke)
5. **Generate Product Prefix NFAs**: Converts the product Buchi automata to prefix NFAs

## Output Files

The script generates the following visualizations:

### Buchi Automata
- `negative_buchi.{dot,png}` - Buchi automaton for ¬φ
- `positive_buchi.{dot,png}` - Buchi automaton for φ
- `kripke_as_buchi.{dot,png}` - Kripke structure as Buchi automaton

### Standalone Prefix NFAs
- `negative_prefix_nfa.{dot,png}` - Prefix NFA from negative Buchi
- `positive_prefix_nfa.{dot,png}` - Prefix NFA from positive Buchi

### Buchi Products
- `product_positive_buchi.{dot,png}` - Positive × Kripke Buchi product
- `product_negative_buchi.{dot,png}` - Negative × Kripke Buchi product

### Product Prefix NFAs
- `prefix_product_nfa_positive.{dot,png}` - Prefix NFA from positive product
- `prefix__product_nfa_negative.{dot,png}` - Prefix NFA from negative product

## JSON Format: Kripke Structure

The Kripke structure format uses **state-based labeling**:

### Required Fields

- `ap`: A list of strings representing the atomic propositions (e.g., `["p", "q"]`)
- `initial_state`: The ID (string) of the initial state
- `states`: A list of state objects. Each state object has:
  - `id`: Unique identifier for the state (string)
  - `labels`: A list of atomic propositions true in this state (e.g., `["p"]`, `["p", "q"]`, or `[]`)
  - `successors`: A list of successor state IDs

### Example: Kripke Structure

```json
{
  "ap": ["p", "q"],
  "initial_state": "s0",
  "states": [
    {
      "id": "s0",
      "labels": ["p", "q"],
      "successors": ["s0", "s1"]
    },
    {
      "id": "s1",
      "labels": ["p"],
      "successors": ["s1", "s2"]
    },
    {
      "id": "s2",
      "labels": ["q"],
      "successors": ["s2", "s3"]
    },
    {
      "id": "s3",
      "labels": [],
      "successors": ["s3", "s0"]
    }
  ]
}
```

## Algorithms

### Buchi to Prefix NFA Conversion

The conversion follows the standard algorithm:

1. **Compute SCCs**: Using Tarjan's algorithm, find all strongly connected components
2. **Identify Accepting SCCs**: An SCC is accepting if it contains at least one edge with acceptance marks
3. **Mark Accepting States**: A state is accepting in the prefix NFA if it can reach an accepting SCC

A finite word is accepted by the prefix NFA if it can be extended to an infinite word accepted by the Buchi automaton.

## Dependencies

- Python 3.x
- [Spot](https://spot.lre.epita.fr/) library for LTL and automata operations
- Graphviz (for visualization)
