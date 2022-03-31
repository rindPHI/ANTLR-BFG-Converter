# Bidirectional Conversion Between ANTLR BGF and a Pivot Language FBF


Grammar-based fuzzing is a common technique to make fuzzers more program-specific. On the one hand, there are different fuzzers with different grammar formats as input and, on the other hand, there are large grammar collections like the Grammar Zoo with its BGF format or repositories with many grammars in ANTLR format. The ability to convert different grammar formats into each other would allow existing grammar collections, and thus thousands of grammars, to be used without requiring additional work for each grammar.
Bidirectional conversion between these different formats is easiest accomplished using a pivot language.
This pivot language can then be used to convert ANTLR to BGF and vice versa, or to convert to any new format by simply developing a new converter for a different format while using the same pivot language.

This converter can convert ANTLR and BGF to a pivot language and vice versa.


# Install dependencies
`git clone`\
`cd antlr-bgf-converter`\
`pip install -r requirements.txt`



# Working Example

The following commands are working examples and should be self-explanatory:\
`python converter.py /input/ANTLR.g4 /output/path antlr fbf`\
`python converter.py /input/BGF /output/path BGF ANTLR `

You can convert any format to any other (except to itself). The last two arguments are case insensitive.


## License
MIT License
