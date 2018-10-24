all: Makefile.coq
	+make -f Makefile.coq all

html: Makefile.coq
	+make -f Makefile.coq html

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject > Makefile.coq

.PHONY: all html clean


# .PHONY : all coq html website clean

# all: coq html website

# html: Makefile.coq
# 	+make -f Makefile.coq html

# clean: Makefile.coq
# 	+make -f Makefile.coq clean
# 	rm -f Makefile.coq

# Makefile.coq: _CoqProject
# 	coq_makefile -f _CoqProject > Makefile.coq

# website: Makefile.coq
# 	+make -f Makefile.coq html
# 	mv html/*html website
# 	rm -rf html

# push: website
# 	rsync -v website/*.html forster@james.ps.uni-saarland.de:~/public_html/itp17
