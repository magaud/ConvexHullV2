# Formalization of a General Recursive Version of the Incremental Algorithm for Convex Hull in Coq

Christophe Brun, Jean-François Dufourd, Nicolas Magaud

This provides a formalization of the incremental algorithm to compute 2D convex hulls using combinatorial maps.
This implementation follows the usual geometry approach to extend the convex hull by traversing the already-constructed hull to find the conflicting edges and update the convex hull accordingly. It uses general recursion for the traversal, and thus is a bit ticker to describe and prove correct formally in Coq.  

Related publication : https://hal.inria.fr/hal-00916880

It compiles with Coq 8.15.2.