MODULES = acqo
PGFILEDESC = "acqo - ant colony query optimization"

PG_CONFIG = pg_config
PGXS := $(shell $(PG_CONFIG) --pgxs)
include $(PGXS)
