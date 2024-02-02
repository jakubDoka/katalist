
## Implementation Brainstorming

Opbvious Requirements:
    - low memory footprint
    - highly parallel
    - inremental
    - advanced compile time features
        - calling functions at compile time
        - inline loops, switches, functions
        - programatical construction of types

### Per File Item Registy

Each file has its own set of datastructures and managed allocations.
    - there is a memory arena for each file that stores slices
    - enumerations are stored in optimized storage where each varinat has its own array, small variants are inlined into the enum index.
    - each scope is an record that can contain functions, fields, and variables, where all of the items can contain expressions.
    - record it self is an expression
    - each record is represented as a packed slice to items it owns + slice to expressions it contains
    - each item tracks how many expressions it contains so we can reserve memory to store types and values in parralel to ast
    - per file registry allows us to efficiently deallocate changed files and reparse + recompile them as needed
