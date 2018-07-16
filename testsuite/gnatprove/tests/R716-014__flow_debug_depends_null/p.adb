with Ada.Text_IO;

package body P with Refined_State => (State => (Arr1,Arr2)) is

   type R is new Integer with Volatile;

   type T is array (1 .. 10) of R;

   Arr1 : T := (others => 0);
   Arr2 : T := (others => 0);
   --  Two constituents ensure that we always generate the Refined_Global for
   --  the Read procedure (ideally, we should not generate it when there is
   --  just one constituent, because then the refinement is obvious).

   procedure Read (Register :     Integer;
                   Value    : out Integer;
                   Verbose  :     Boolean)
   is
   begin
      Value := Integer (Arr1 (Register));
      pragma Debug (Verbose, Ada.Text_IO.Put_Line ("Read"));
   end;
end;
