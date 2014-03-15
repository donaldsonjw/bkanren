
SYSTEM := $(shell uname -s)

#TOOLS
BIGLOO = bigloo
BGLAFILE = bglafile
BGLJFILE = bgljfile
BGLTAGS = bgltags

ifeq ($(SYSTEM), DARWIN) 
   LD = clang
   LDOPT = -dynamiclib -single_module -Wl,-read_only_relocs,suppress
   SHAREDSUFFIX = dylib
else ifeq ($(SYSTEM), MINGW32_NT-6.0)
   LD = gcc
   LDOPT = -shared
   SHAREDSUFFIX = dll
else # Linux
   LD = gcc
   LDOPT = -shared
   SHAREDSUFFIX = so
endif


AR = ar 
RANLIB = ranlib
INSTALL = install
LINK = ln
JAR = jar



BIGLOO_VERSION := $(shell $(BIGLOO) -eval "(print *bigloo-version*) (exit 0)" -q)
BIGLOOLIBDIR := $(shell $(BIGLOO) -eval "(print *default-lib-dir*) (exit 0)" -q)

BIGLOOGC := $(shell $(BIGLOO) -eval "(print *gc-lib*) (exit 0)" -q)-$(BIGLOO_VERSION)

BIGLOOSRUNLIB := bigloo_s-$(BIGLOO_VERSION)

BIGLOOURUNLIB := bigloo_s-$(BIGLOO_VERSION)

#install related variables
DESTDIR = /usr
INSTLIBDIR = $(DESTDIR)/lib
INSTBIGLOOLIBDIR = $(INSTLIBDIR)/bigloo/$(BIGLOO_VERSION)




#Bigloo Flags
BHEAPFLAGS = -I src/Llib -unsafe -q -mkaddheap -mkaddlib -v2 \
	     -heap-library $(LIBNAME)

BCOMMONFLAGS = -mkaddlib -fsharing -q \
               -copt '$(CCOMMONFLAGS)' -I src/Llib

BSAFEFLAGS = $(BCOMMONFLAGS) -cg -O3 -g 

BUNSAFEFLAGS = $(BCOMMONFLAGS) -O4 -unsafe

#C Flags
CCOMMONFLAGS = -fPIC

# directory variables
OBJDIR = objs
DISTDIR = dist
SCLASSDIR = classes_s/bigloo/$(LIBNAME)
UCLASSDIR = classes_u/bigloo/$(LIBNAME)
ESCLASSDIR = classes_es/bigloo/$(LIBNAME)
EUCLASSDIR = classes_eu/bigloo/$(LIBNAME)

# sources
BIGLOOSRCS = $(wildcard src/Llib/*.scm)
HEAPSRC = src/Misc/make_lib.scm


# object files

_SRCSWOUTDIR = $(foreach src, $(BIGLOOSRCS), $(notdir $(src)))
_BASEOBJSWOUTDIR = $(_SRCSWOUTDIR:%.scm=%)

SAFEOBJECTS = $(_BASEOBJSWOUTDIR:%=$(OBJDIR)/%_s.o)

UNSAFEOBJECTS = $(_BASEOBJSWOUTDIR:%=$(OBJDIR)/%_u.o)

SAFECLASSES = $(_BASEOBJSWOUTDIR:%=$(SCLASSDIR)/%.class)
UNSAFECLASSES = $(_BASEOBJSWOUTDIR:%=$(UCLASSDIR)/%.class)

_ESRCSWOUTDIR = $(foreach src, $(HEAPSRC), $(notdir $(src)))
_EBASEOBJSWOUTDIR = $(_ESRCSWOUTDIR:%.scm=%)

ESAFEOBJECTS = $(_EBASEOBJSWOUTDIR:%=$(OBJDIR)/%_s.o)

EUNSAFEOBJECTS = $(_EBASEOBJSWOUTDIR:%=$(OBJDIR)/%_u.o)

ESAFECLASSES = $(_EBASEOBJSWOUTDIR:%=$(ESCLASSDIR)/%.class)

EUNSAFECLASSES = $(_EBASEOBJSWOUTDIR:%=$(EUCLASSDIR)/%.class)


.SUFFIXES:

$(OBJDIR)/%_s.o:src/Llib/%.scm
	$(BIGLOO) -c $(BSAFEFLAGS) -o $@ $^

$(OBJDIR)/%_u.o:src/Llib/%.scm
	$(BIGLOO) -c $(BUNSAFEFLAGS) -o $@ $^

$(SCLASSDIR)/%.class:src/Llib/%.scm
	$(BIGLOO) -jvm -c $(BSAFEFLAGS) -o $@ $^

$(UCLASSDIR)/%.class:src/Llib/%.scm
	$(BIGLOO) -jvm -c $(BUNSAFEFLAGS) -o $@ $^



#targets

c: .afile .etags lib recette/test$(LIBNAME)

jvm: .jfile .afile .etags libj

all: c jvm


.afile: $(BIGLOOSRCS)
	$(BGLAFILE) -o $@  $^

.jfile: $(BIGLOOSRCS)
	$(BGLJFILE) -pbase bigloo.$(LIBNAME) -o $@  -I src/Misc -I src/Llib $(_SRCSWOUTDIR)

.etags: $(BIGLOOSRCS)
	$(BGLTAGS) -o $@ $^

heap: $(DISTDIR)/$(LIBNAME).heap 

jheap: $(DISTDIR)/$(LIBNAME).jheap 

$(DISTDIR)/$(LIBNAME).heap: $(DISTDIR) $(HEAPSRC)
	$(BIGLOO) $(BHEAPFLAGS) $(HEAPSRC)  -addheap $@

$(DISTDIR)/$(LIBNAME).jheap: $(DISTDIR) $(HEAPSRC)
	$(BIGLOO) -jvm $(BHEAPFLAGS) $(HEAPSRC)  -addheap $@


$(OBJDIR)/make_lib_s.o:src/Misc/make_lib.scm
	$(BIGLOO) -c $(BSAFEFLAGS) -o $@ $^

$(ESCLASSDIR)/make_lib.class:src/Misc/make_lib.scm
	$(BIGLOO) -jvm -c $(BSAFEFLAGS) -o $@ $^

$(OBJDIR)/make_lib_u.o:src/Misc/make_lib.scm
	$(BIGLOO) -c $(BUNSAFEFLAGS) -o $@ $^

$(EUCLASSDIR)/make_lib.class:src/Misc/make_lib.scm
	$(BIGLOO) -jvm -c $(BUNSAFEFLAGS) -o $@ $^


lib: init heap lib_s lib_u lib_s.a lib_u.a lib_es lib_eu 

libj: init jheap heap jar_s jar_u jar_es jar_eu

init: $(DISTDIR) $(DISTDIR)/$(LIBNAME).init

$(DISTDIR)/$(LIBNAME).init : src/Llib/*.sch src/Misc/$(LIBNAME).init.in
	cat $^ > $@

jar_s: $(SCLASSDIR)  $(DISTDIR) $(SAFECLASSES)
	$(JAR) -cf $(DISTDIR)/$(LIBNAME)_s-$(VERSION).zip -C $(SCLASSDIR)/../../ .

jar_u: $(UCLASSDIR) $(EUCLASSDIR) $(DISTDIR) $(UNSAFECLASSES)
	$(JAR) -cf $(DISTDIR)/$(LIBNAME)_u-$(VERSION).zip -C $(UCLASSDIR)/../../ .   

jar_es : $(ESCLASSDIR) $(DISTDIR) $(ESAFECLASSES)
	$(JAR) -cf $(DISTDIR)/$(LIBNAME)_es-$(VERSION).zip -C $(ESCLASSDIR)/../../ . 


jar_eu : $(UCLASSDIR) $(DISTDIR) $(EUNSAFECLASSES)
	$(JAR) -cf $(DISTDIR)/$(LIBNAME)_eu-$(VERSION).zip -C $(UCLASSDIR)/../../ .


lib_s: $(OBJDIR) $(DISTDIR) $(SAFEOBJECTS)
	$(LD) $(LDOPT) -o $(DISTDIR)/lib$(LIBNAME)_s-$(VERSION).$(SHAREDSUFFIX) $(SAFEOBJECTS) -L$(BIGLOOLIBDIR) -l$(BIGLOOSRUNLIB) -l$(BIGLOOGC) -lc -lm

lib_s.a : $(OBJDIR) $(DISTDIR) $(SAFEOBJECTS)
	$(AR) qcv $(DISTDIR)/lib$(LIBNAME)_s-$(VERSION).a $(SAFEOBJECTS);\
	$(RANLIB) $(DISTDIR)/lib$(LIBNAME)_s-$(VERSION).a

lib_es : $(OBJDIR) $(DISTDIR) $(ESAFEOBJECTS)
	$(LD) $(LDOPT) -o $(DISTDIR)/lib$(LIBNAME)_es-$(VERSION).$(SHAREDSUFFIX) $(ESAFEOBJECTS) -L$(BIGLOOLIBDIR)  -L$(DISTDIR) -l$(LIBNAME)_s-$(VERSION) -l$(BIGLOOSRUNLIB) -l$(BIGLOOGC) -lc -lm

lib_u : $(OBJDIR) $(DISTDIR) $(UNSAFEOBJECTS)
	$(LD) $(LDOPT) -o $(DISTDIR)/lib$(LIBNAME)_u-$(VERSION).$(SHAREDSUFFIX) $(UNSAFEOBJECTS) -L$(BIGLOOLIBDIR) -l$(BIGLOOURUNLIB) -l$(BIGLOOGC) -lc -lm

lib_u.a : $(OBJDIR) $(DISTDIR) $(UNSAFEOBJECTS)
	$(AR) qcv $(DISTDIR)/lib$(LIBNAME)_u-$(VERSION).a $(SAFEOBJECTS);\
	$(RANLIB) $(DISTDIR)/lib$(LIBNAME)_u-$(VERSION).a

lib_eu : $(OBJDIR) $(DISTDIR) $(EUNSAFEOBJECTS)
	$(LD) $(LDOPT) -o $(DISTDIR)/lib$(LIBNAME)_eu-$(VERSION).$(SHAREDSUFFIX) $(EUNSAFEOBJECTS) -L$(BIGLOOLIBDIR) -L$(DISTDIR) -l$(LIBNAME)_u-$(VERSION) -l$(BIGLOOURUNLIB) -l$(BIGLOOGC) -lc -lm


recette/test$(LIBNAME) : recette/test$(LIBNAME).scm lib 
	$(BIGLOO) -static-all-bigloo $(BUNSAFEFLAGS) -L $(DISTDIR) -o $@ $< 


$(OBJDIR):
	mkdir -p $@

$(DISTDIR):
	mkdir -p $@

$(SCLASSDIR):
	mkdir -p $@

$(UCLASSDIR):
	mkdir -p $@

$(ESCLASSDIR):
	mkdir -p $@

$(EUCLASSDIR):
	mkdir -p $@


check-syntax: .afile
	$(BIGLOO) -afile .afile -syntax-check -L $(DISTDIR) ${CHK_SOURCES}



install: all
	for file in $(DISTDIR)/*; do \
	  $(INSTALL) $$file $(INSTBIGLOOLIBDIR)/`basename $$file`; \
	done; \
	for file in $(DISTDIR)/*.$(SHAREDSUFFIX); do \
	  $(LINK) -s $(INSTBIGLOOLIBDIR)/`basename $$file` $(INSTLIBDIR)/`basename $$file`; \
	done

clean:
	rm -f -r $(OBJDIR);\
	rm -f .afile;\
	rm -f .jfile;\
	rm -f -r $(DISTDIR);\
	rm -f -r $(SCLASSDIR);\
	rm -f -r $(UCLASSDIR);\
	rm -f $(LIBNAME).heap;\
	rm -f $(LIBNAME).jheap;\
	rm -f $(LIBNAME).init;\
	rm -f recette/test$(LIBNAME)



