# bkanren Readme


## Description

bkanren is a port of minikanren as found at <https://github.com/miniKanren/miniKanren> to Bigloo Scheme. For detailed information on minikanren, please visit <http://minikanren.org/>.


It supports the following operators:

### Logical Operators

* fresh
* eigen
* conde

### Extra-logical Operators

* project
* ground?

### Interface Operators

* run
* run*

### Constraint Operators

* =/= 
* symbolo
* numbero
* stringo
* absento

### Operators from The Reasoned Schemer

* caro
* cdro
* conso
* nullo
* eqo
* pairo
* listo
* lolo
* twinso
* listofo
* loto
* membero
* eq-caro
* memo
* rembero
* appendo
* unwrapo
* swappendo
* flatteno
* flattenrevo
* anyo
* nevero
* alwayso
* salo


### Building

Both the Bigloo native and jvm backends are supported. To build the native libraries, just execute

    make

To build the jvm libraries, execute

	make jvm

To build both, execute

	make all


### Installation

To Install the libraries, execute

	make install

This by default installs the libraries into the directory /usr/lib/bigloo/<bigloo-version>. If you have Bigloo installed to a different prefix, execute

	make install DESTDIR=/path/prefix

This will result in the libraries being installed to /path/prefix/lib/bigloo/<bigloo-version>.

### Interpretor

The bkanren library can be dynamically loaded into the interpretor with

	(library-load 'bkanren)

If you have not installed the bkanren library in a standard location, you may need to pass path as a second argument.

	(libary-load 'bkanren "/path/to/libdir")


