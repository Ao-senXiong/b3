all: html

# add -r to say to rebuild

pdf:
	madoko -vv --pdf --odir=out krml301

html:
	madoko -vv --odir=out krml301
	madoko -vv --odir=out krml304

clean:
	rm -rf out
