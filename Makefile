# Only compile by default.
all: compile

# Type-checking correspondence.agda effectively checks the full
# mechanization.
compile:
	agda src/README.agda

# Generate a hyperlinked and highlighted version HTML of the code.
doc:
	agda --html src/README.agda

# FIXME @Blaisorblade ;-)
clean:

.PHONY: all clean compile doc
