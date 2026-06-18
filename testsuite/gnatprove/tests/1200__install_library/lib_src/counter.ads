package Counter
  with SPARK_Mode
is

   --  No Global contracts are given here on purpose: the global effects on the
   --  hidden state are discovered by GNATprove's global generation and stored
   --  in the summary ALI files.

   procedure Bump (Amount : Natural);
   --  Increase the internal counter by Amount, saturating on overflow

   function Value return Natural;
   --  Return the current value of the internal counter

end Counter;
