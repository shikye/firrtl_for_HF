root_dir ?= $(PWD)
regress_dir ?= $(root_dir)/regress
install_dir ?= $(root_dir)/utils/bin

SBT ?= sbt
SBT_FLAGS ?= -Dsbt.log.noformat=true

scala_jar ?= $(install_dir)/firrtl.jar
scala_src := $(shell find src -type f \( -name "*.scala" -o -path "*/resources/*" \))

build:	build-scala

clean:
	$(MAKE) -C $(root_dir)/spec clean
	rm -f $(install_dir)/firrtl.jar
	$(SBT) "clean"

.PHONY : specification
specification:
	$(MAKE) -C $(root_dir)/spec all

regress: $(scala_jar)
	cd $(regress_dir) && $(install_dir)/firrtl -i rocket.fir -o rocket.v -X verilog

# Scala Added Makefile commands

build-scala: $(scala_jar)

$(scala_jar): $(scala_src)
	$(SBT) "assembly"

test-scala:
	$(SBT) test

jenkins-build:	clean
	$(SBT) $(SBT_FLAGS) +clean +test +publish-local
	$(SBT) $(SBT_FLAGS) coverageReport


modify:
	$(SBT) compile
	$(SBT) assembly
	./utils/bin/firrtl -i ~/nutshell-difuzz/NutShell.fir -td ~/nutshell-difuzz/ -fct coverage.regCoverage -X verilog -faf ~/nutshell-difuzz/NutShell.anno.json --allow-unrecognized-annotations -o ~/nutshell-difuzz/out.v > ~/nutshell-difuzz/log


.PHONY: build clean regress build-scala test-scala modify
