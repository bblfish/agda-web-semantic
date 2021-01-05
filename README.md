Agda Semantic Web Libraries
===========================

These libraries are intended to support processing of semantic web data in Agda,
and to ensure that all such data satisfies its integrity constraints, expressed
as an ontology.

The data is expressed in terms of the W3C Resource Description Framework (RDF),
and ontologies are expressed in terms of the W3C Web Ontology Language (OWL).

The semantics of RDF and OWL are given as Description Logics,
formalized in the Web.Semantic.DL library.

An overview of this library can be found in 

> Jeffrey, A. S. A., and Peter F. Patel-Schneider. 
["Integrity constraints for linked data."](http://ceur-ws.org/Vol-745/paper_31.pdf)
Proc. Int. Workshop Description Logics. 2011.
	

The Abstract from the article

> Linked Data makes one central addition to the Semantic Web principles: all entity URIs should be dereferenceable to provide an authoritative RDF representation. URIs in a linked dataset can be partitioned into the exported URIs for which the dataset is authoritative versus the imported URIs the dataset is linking against. This partitioning has an impact on integrity constraints, as a Closed World Assumption applies to the exported URIs, while a Open World Assumption applies to the imported URIs. We provide a definition of integrity constraint satisfaction in the presence of partitioning, and show that it leads to a formal interpretation of dependency graphs which describe the hyperlinking relations between datasets. We prove that datasets with integrity constraints form a symmetric monoidal category, from which the soundness of acyclic dependency graphs follows.

