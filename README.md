# Custom NFA Definition Format

## JSON Structure

The JSON file must contain the following top-level keys:

- `ap`: A list of strings representing the atomic propositions (e.g., `["p", "q"]`).
- `initial_state`: The ID (string or integer) of the initial state.
- `states`: A list of state objects. Each state object has:
  - `id`: Unique identifier for the state (string or integer).
  - `transitions`: A list of transition objects, each with:
    - `dst`: The destination state ID.
    - `cond`: A logical formula string representing the condition.
- `accepting_states`: A list of state IDs that are accepting.

## Boolean Logic Syntax

The `cond` field in transitions supports standard Boolean logic operators parsed by the `spot` library:

| Operator | Syntax | Example | Description |
| :--- | :--- | :--- | :--- |
| **Negation** | `!` | `!p` | True if `p` is false |
| **Conjunction (AND)** | `&` or `&&` | `p & q` | True if both are true |
| **Disjunction (OR)** | `|` or `||` | `p | q` | True if at least one is true |
| **Implication** | `->` | `p -> q` | Equivalent to `!p | q` |
| **Equivalence** | `<->` | `p <-> q` | True if both are equal |
| **XOR** | `xor` | `p xor q` | True if exactly one is true |
| **True** | `1` or `true` | `1` | Always matches (unconditional transition) |
| **False** | `0` or `false` | `0` | Never matches |

Parentheses `(...)` can be used to group expressions.

## Example

```json
{
  "ap": ["p", "q"],
  "initial_state": "S0",
  "states": [
    {
      "id": "S0",
      "transitions": [
        { "dst": "S1", "cond": "p -> q" },
        { "dst": "S0", "cond": "!p & (q | r)" }
      ]
    },
    {
      "id": "S1",
      "transitions": [
        { "dst": "S1", "cond": "1" } 
      ]
    }
  ],
  "accepting_states": ["S1"]
}
```
