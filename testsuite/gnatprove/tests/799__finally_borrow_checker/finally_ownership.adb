procedure Finally_Ownership with SPARK_Mode is
   type Cell;
   type Tree is access Cell;
   type Cell is record
      Content : Integer;
      Left : Tree;
      Right : Tree;
   end record;
   procedure OK (X : Tree);
   procedure KO (X : Tree);
   procedure KO2 (X : Tree);
   procedure KO3 (X : Tree);
   procedure KO4 (X : Tree);
   function KO5 (X : Tree) return Boolean with Side_Effects;
   function KO6 (X : Tree) return Boolean with Side_Effects;
   procedure KO7 (X : Tree);
   procedure KO8 (X : Tree);
   procedure KO9 (X : Tree);
   procedure KO10 (X : Tree);
   procedure KO11 (X : Tree);
   function KO12 (X : Tree) return Boolean with Side_Effects;
   function KO13 (X : Tree) return Boolean with Side_Effects;


   procedure OK (X : Tree) is
      Y : Tree;
   begin
      if X = null or else X.Left = null then
         return;
      end if;
      declare
         R : Tree := X.Right;
      begin
         if X.Content = 0 then
            Y := X.Left.Left;
            goto A;
         else
            Y := X.Left.Right;
            goto B;
         end if;
      finally
         X.Right := R;
      end;
      <<A>>
      X.Left.Left := Y;
      goto C;
      <<B>>
      X.Left.Right := Y;
      <<C>>
   end OK;

   procedure KO (X : Tree) is
      Y : Tree;
   begin

      begin
         if X.Content = 0 then
            return;
         end if;
      finally
         Y := X.Right;
      end;
      X.Right := Y;

   finally
      X.Right.Content := 1;
   end;

   procedure KO2 (X : Tree) is
      Y : Tree;
   begin
      begin
         begin
            if X.Content = 0 then
               goto L;
            end if;
            finally
              Y := X.Right;
         end;
         X.Right := Y;

         finally
           X.Right.Content := 1;
      end;
      <<L>>
   end;

   procedure KO3 (X : Tree) is
      Y : Tree;
   begin
      loop
         begin
            begin
               if X.Content = 0 then
                  exit;
               end if;
            finally
               Y := X.Right;
            end;
            X.Right := Y;

         finally
            X.Right.Content := 1;
         end;
      end loop;
   end;

   procedure KO4 (X : Tree) is
      Y : Tree;
      E : exception;
   begin
      begin
         begin
            if X.Content = 0 then
               raise E;
            end if;
            finally
              Y := X.Right;
         end;
         X.Right := Y;

      finally
         X.Right.Content := 1;
      end;
   exception
      when E =>
         null;
   end;

   function KO5 (X : Tree) return Boolean is
      Y : Tree;
      E : exception;
   begin
      begin
         if X.Content = 0 then
            return B : Boolean := True do
               null;
            end return;
         end if;
         finally
           Y := X.Right;
      end;
      X.Right := Y;
      return True;

      finally
         X.Right.Content := 1;
   end;

   function KO6 (X : Tree) return Boolean is
      Y : Tree;
      E : exception;
   begin
      return B : Boolean := True do
         begin
            if X.Content = 0 then
               return;
            end if;
            finally
              Y := X.Right;
         end;
         X.Right := Y;

      finally
         X.Right.Content := 1;
      end return;
   end;

   procedure KO7 (X : Tree) is
      Y : Tree := new Cell'(Content => 0, Left => null, Right => null);
   begin
      X.Left := Y;
   finally
      Y.Content := 1;
   end;

   procedure KO8 (X : Tree) is
      Y : Tree := new Cell'(Content => 0, Left => null, Right => null);
   begin
      if X.Content = 0 then
         X.Left := Y;
         return;
      end if;
   finally
      Y.Content := 1;
   end;

   procedure KO9 (X : Tree) is
      Y : Tree := new Cell'(Content => 0, Left => null, Right => null);
      E : exception;
   begin
      begin
         if X.Content = 0 then
            X.Left := Y;
            raise E;
         end if;
         finally
           Y.Content := 1;
      end;
   exception
      when E => null;
   end;

   procedure KO10 (X : Tree) is
      Y : Tree := new Cell'(Content => 0, Left => null, Right => null);
      E : exception;
   begin
      loop
         begin
            if X.Content = 0 then
               X.Left := Y;
               exit;
            end if;
            finally
              Y.Content := 1;
         end;
      end loop;
   end;

   procedure KO11 (X : Tree) is
      Y : Tree := new Cell'(Content => 0, Left => null, Right => null);
      E : exception;
   begin
      begin
         if X.Content = 0 then
            X.Left := Y;
            goto L;
         end if;
         finally
           Y.Content := 1;
      end;
      <<L>>
   end;

   function KO12 (X : Tree) return Boolean is
      Y : Tree := new Cell'(Content => 0, Left => null, Right => null);
      E : exception;
   begin
      if X.Content = 0 then
         X.Left := Y;
         return B : Boolean := True do
            null;
         end return;
      end if;
      return True;
   finally
      Y.Content := 1;
   end;

   function KO13 (X : Tree) return Boolean is
      Y : Tree := new Cell'(Content => 0, Left => null, Right => null);
      E : exception;
   begin
      return B : Boolean := True do
         begin
            if X.Content = 0 then
               X.Left := Y;
               return;
            end if;
         finally
           Y.Content := 1;
         end;
      end return;
   end;

begin
   null;
end Finally_Ownership;
