package body Pkg
with
  SPARK_Mode    => On,
  Refined_State => (State => Counter)
is

   Counter : Natural := Natural'First;

   -------------------------------------------------------------------------

   procedure Process
     with
       SPARK_Mode      => On,
       Refined_Global  => (In_Out  => Counter),
     Refined_Depends => (Counter => + null)
   is
   begin
      if Counter < Natural'Last then
         Counter := Counter + 1;
      else
         Counter := Natural'First;
      end if;
   end Process;

end Pkg;
