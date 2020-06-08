package Weird is

   procedure P (B : Boolean) with
     Annotate => (GNATprove, Terminating),
     Annotate => (GNATprove, Might_Not_Return);
   --  Having both Terminating and Might_Not_Return doesn't make sense

   procedure Q (B : Boolean) with
     Annotate => (GNATprove, Might_Not_Return),
     Annotate => (GNATprove, Terminating);
   --  Just like above, but in different order

   procedure R (B : Boolean) with
     Annotate => (GNATprove, Terminating),
     No_Return;
   --  Terminating and No_Return is incompatible as well (just like
   --  Might_Not_Return and No_Return, but we already have a test for this).

end Weird;
