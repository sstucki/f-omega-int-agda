# Only compile by default.
all: compile

# Type-checking correspondence.agda effectively checks the full
# mechanization.
compile:
	agda src/Correspondence.agda

# Generate a hyperlinked and highlighted version HTML of the code.
doc:
	agda --html src/Correspondence.agda

# FIXME @Blaisorblade ;-)
clean:

.PHONY: all clean compile doc
