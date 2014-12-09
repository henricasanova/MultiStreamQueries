default:
	@echo "make gzip       # compress all datafiles"
	@echo "make gunzip     # uncompress all datafiles"

gzip:
	find . -name "*TREE*" | grep -v gz | xargs gzip

gunzip:
	find . -name "*TREE*.gz" | xargs gunzip 
