# Only compile by default.
all: compile

# Type-checking correspondence.agda effectively checks the full
# mechanization.
compile:
	agda src/Correspondence.agda

# Generate a hyperlinked and highlighted version HTML of the code.
doc:
	agda --html src/Correspondence.agda

# Remove build products
clean:
	# Remove interface files
	find . -name '*.agdai'|xargs rm
	# Remove build folder altogether?
	#rm -rf _build

.PHONY: all clean compile doc
