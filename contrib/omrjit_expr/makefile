MODULES = omrjit_expr

PGFILEDESC = "omrjit_expr - tuple deformation"

JITBUILDER_DIR = /home/debajyoti/vm-project/src/lib/omr_debug/omr/jitbuilder/release/cpp

OMR_CXXFLAGS  += --std=c++0x 
CXXFLAGS += $(OMR_CXXFLAGS) 
OMR_CPPFLAGS = -D__STDC_LIMIT_MACROS -D__STDC_FORMAT_MACROS -D__STDC_CONSTANT_MACROS -D_DEBUG -D_GNU_SOURCE -I/home/debajyoti/vm-project/src/lib/omr_debug/omr/include_core -I/home/debajyoti/vm-project/src/lib/omr_debug/omr/jitbuilder/release/cpp/include
override CPPFLAGS := $(OMR_CPPFLAGS) $(CPPFLAGS)
OMR_LDFLAGS = -L$(JITBUILDER_DIR) -ljitbuilder -ldl
override LDFLAGS := $(OMR_LDFLAGS) $(LDFLAGS)
override COMPILER = $(CXX) $(CFLAGS)


ifdef USE_PGXS
PG_CONFIG = pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
else
subdir = contrib/omrjit_expr
top_builddir = ../..
include $(top_builddir)/src/Makefile.global
include $(top_srcdir)/src/Makefile.shlib
include $(top_srcdir)/contrib/contrib-global.mk
endif
