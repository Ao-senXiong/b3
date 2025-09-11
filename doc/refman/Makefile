SPHINXBUILD = sphinx-build
SOURCEDIR = .
BUILDDIR = _build

html:
	$(SPHINXBUILD) -b html $(SOURCEDIR) $(BUILDDIR)/html
	cp ../out/krml301.html $(BUILDDIR)/html
	cp ../out/krml304.html $(BUILDDIR)/html

clean:
	rm -rf $(BUILDDIR)

.PHONY: html clean
