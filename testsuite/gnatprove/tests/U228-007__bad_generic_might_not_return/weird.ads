package Weird is

   generic
   procedure PG (B : Boolean) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Might_Not_Return);
   --  Having both Terminating and Might_Not_Return doesn't make sense

   generic
   procedure QG (B : Boolean) with
     Annotate => (GNATprove, Might_Not_Return),
     Annotate => (GNATprove, Always_Return);
   --  Just like above, but in different order

   generic
   procedure RG (B : Boolean) with
     Annotate => (GNATprove, Always_Return),
     No_Return;
   --  Terminating and No_Return is incompatible as well (just like
   --  Might_Not_Return and No_Return, but we already have a test for this).

end Weird;
