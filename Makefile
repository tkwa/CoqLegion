default: map definitions theorem1 theorem2 theorem3

map:
	coqc -Q . Legion Map.v

definitions:
	coqc -Q . Legion Definitions.v

theorem1:
	coqc -Q . Legion theorem1.v

theorem2:
	coqc -Q . Legion theorem2.v

theorem3:
	coqc -Q . Legion theorem3.v
