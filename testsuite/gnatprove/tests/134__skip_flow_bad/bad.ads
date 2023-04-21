package Bad is

   function F return Boolean with Import;

   procedure P with Annotate => (Gnatprove, Skip_Flow_And_Proof);

end Bad;
