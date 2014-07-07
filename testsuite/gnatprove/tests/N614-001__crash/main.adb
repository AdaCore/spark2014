with Part; use Part;
with Ada.Text_IO;

procedure Main is

   procedure Print_Set (X : Set);

   procedure Print_Part (P : Partition);

   ---------------
   -- Print_Set --
   ---------------

   procedure Print_Set (X : Set) is
      use Ada.Text_IO;
   begin
      Put ("{ ");
      for Elt of X loop
         Put (Elt'Img);
      end loop;
      Put_Line (" }");
   end Print_Set;

   procedure Print_Part (P : Partition) is
      use Ada.Text_IO;
   begin
      Put ("[ ");
      for Elt of P loop
         Put (Elt'Img);
      end loop;
      Put_Line (" ]");
   end Print_Part;

   A : Set :=
     (1 => 22, 2 => 33, 3 => 100, 4 => 55, 5 => 44, 6 => 11);
   X : Set :=
     (1 => 11, 2 => 22, 3 => 44);
   Part : Partition := (1 => 4);
   NP : Partition (1 .. 5);
   Count : Natural;
begin
   Print_Set (A);
   Refine (A, Part, X, NP, Count);
   Print_Set (A);
   Print_Part (NP (1 .. Count));
end Main;
