pragma Extensions_Allowed (All_Extensions);
procedure Main with SPARK_Mode is
   function Random (X : Integer) return Boolean
     with Import, Global => null;
   type Cell;
   type Tree is access Cell;
   type Cell is record
      V : Integer;
      L : Tree;
      R : Tree;
   end record;
   procedure KO_1 (X : in out Tree);
   procedure KO_2 (X : in out Tree);
   procedure KO_3 (X : in out Tree);
   procedure KO_4 (X : in out Tree);
   procedure KO_5 (X : in out Tree);
   procedure OK_1 (X : in out Tree);
   procedure KO_1 (X : in out Tree) is
   begin
      loop
         declare
            Y : Tree := X;
         begin
            continue when Random (Y.V);
            X := Y;
         end;
      end loop;
   end KO_1;
   procedure KO_2 (X : in out Tree) is
   begin
      loop
         continue when Random (X.V);
         declare
            Y : Tree := X;
         begin
            null;
         end;
      end loop;
   end KO_2;
   procedure KO_3 (X : in out Tree) is
   begin
      Outer: loop
         declare
            Y_O : access Cell := X;
            Z_O: Tree := Y_O.L;
         begin
            Medium : loop
               declare
                  Y_M : access Cell := Y_O.R;
                  Z_M : Tree := Y_M.L;
               begin
                  Inner : loop
                     declare
                        Y_I : access Cell := Y_M.R;
                        Z_I : Tree := Y_I.L;
                     begin
                        continue Medium when Random (Z_I.V);
                        --  Skip restoration of Y_I/Y_M borrowers.

                        Y_I.L := Z_I;
                     end;
                  end loop Inner;
                  Y_M.L := Z_M;
               end;
            end loop Medium;
            Y_O.L := Z_O;
         end;
      end loop Outer;
   end KO_3;
   procedure KO_4 (X : in out Tree) is
   begin
      Outer: loop
         declare
            Y_O : access Cell := X;
            Z_O: Tree := Y_O.L;
         begin
            Medium : loop
               declare
                  Y_M : access Cell := Y_O.R;
                  Z_M : Tree := Y_M.L;
               begin
                  Inner : loop
                     declare
                        Y_I : access Cell := Y_M.R;
                     begin
                        continue Medium when Random (Y_I.V);
                        --  Skip restoration of Y_M borrower

                     end;
                  end loop Inner;
                  Y_M.L := Z_M;
               end;
            end loop Medium;
            Y_O.L := Z_O;
         end;
      end loop Outer;
   end KO_4;

   procedure KO_5 (X : in out Tree) is
   begin
      Outer: loop
         declare
            Y_O : access Cell := X;
            Z_O: Tree := Y_O.L;
         begin
            Medium : loop
               declare
                  Y_M : access Cell := Y_O.R;
               begin
                  Inner : loop
                     declare
                        Y_I : access Cell := Y_M.R;
                        Z_I : Tree := Y_I.L;
                     begin
                        continue Medium when Random (Z_I.V);
                        --  Skip restoration of Y_I borrower

                        Y_I.L := Z_I;
                     end;
                  end loop Inner;
               end;
            end loop Medium;
            Y_O.L := Z_O;
         end;
      end loop Outer;
   end KO_5;

   procedure OK_1 (X : in out Tree) is
      Y : Tree := X;
   begin
      loop
         X := Y;
         Y := X;
         begin
            continue when Random (Y.V);
            X := Y;
            exit;
         end;
      end loop;
   end OK_1;

   procedure OK_2 (X : in out Tree) is
   begin
      Outer: loop
         declare
            Y_O : access Cell := X;
            Z_O: Tree := Y_O.L;
         begin
            Medium : loop
               declare
                  Y_M : access Cell := Y_O.R;
               begin
                  Inner : loop
                     declare
                        Y_I : access Cell := Y_M.R;
                     begin
                        continue Medium when Random (Y_I.V);

                     end;
                  end loop Inner;
               end;
            end loop Medium;
            Y_O.L := Z_O;
         end;
      end loop Outer;
   end OK_2;

   procedure OK_3 (X : in out Tree) is
   begin
      loop
         declare
            Y : Tree := X;
         begin
            if Y.V = 0 then
               X := Y;
               continue;
            end if;
            X := Y;
         end;
      end loop;
   end OK_3;

   procedure KO_6 (X : in out Tree) is
   begin
      loop
         declare
            Y : Tree := X;
         begin
            if Y.V = 0 then
               X := Y;
               continue when Random (X.V);
            end if;
            X := Y;
         end;
      end loop;
   end KO_6;

   procedure OK_5 (X : in out Tree) is
   begin
     Outer: loop
         declare
            Y : Tree := X;
         begin
            while Random (Y.V) loop
               if Y.V = 0 then
                  X := Y;
                  continue Outer;
               end if;
            end loop;
            X := Y;
         end;
      end loop Outer;
   end OK_5;

   procedure KO_7 (X : in out Tree) is
   begin
     Outer: loop
         declare
            Y : Tree := X;
         begin
            while Random (Y.V) loop
               if Y.V = 0 then
                  X := Y;
                  continue Outer when Random (X.V);
               end if;
            end loop;
            X := Y;
         end;
      end loop Outer;
   end KO_7;

begin
   null;
end Main;
