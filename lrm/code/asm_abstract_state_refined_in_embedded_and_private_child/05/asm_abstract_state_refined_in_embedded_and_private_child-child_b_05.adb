
package body Power.Source_B
is
   State : Integer;

   procedure Read (Level : out Integer)
   is
   begin
      Level := State;
   end Read;
end Power.Source_B;
