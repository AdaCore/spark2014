with Ada.Containers; use Ada.Containers;
with Ada.Containers.Functional_Sets;

procedure Binary_Search with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Tree;
   type Tree_Acc is access Tree;
   type Tree is record
      Data  : Integer;
      Left  : Tree_Acc;
      Right : Tree_Acc;
   end record;

   function At_End_Borrow (T : access constant Tree) return access constant Tree is
     (T)
   with Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   function M_Contains (T : access constant Tree; V : Integer) return Boolean is
      (if T = null then False
       else V = T.Data or else M_Contains (T.Left, V) or else M_Contains (T.Right, V))
   with Annotate => (GNATprove, Terminating),
     Ghost;

   function "<" (V : Integer; T : access constant Tree) return Boolean
     with Annotate => (GNATprove, Terminating),
     Ghost,
     Post => "<"'Result =
       (for all I in Integer => (if M_Contains (T, I) then V < I))
     and "<"'Result =
       (T = null or else (V < T.Data and V < T.Left and V < T.Right))
   is
   begin
      if T = null then
         return True;
      else
         pragma Assert (for all I in Integer =>
                          (if M_Contains (T.Left, I) then M_Contains (T, I)));
         pragma Assert (for all I in Integer =>
                          (if M_Contains (T.Right, I) then M_Contains (T, I)));
         return V < T.Data and V < T.Left and V < T.Right;
      end if;
   end "<";

   function "<" (T : access constant Tree; V : Integer) return Boolean
     with Annotate => (GNATprove, Terminating),
     Ghost,
     Post => "<"'Result =
       (for all I in Integer => (if M_Contains (T, I) then I < V))
     and "<"'Result =
       (T = null or else (T.Data < V and T.Left < V and T.Right < V))
   is
   begin
      if T = null then
         return True;
      else
         pragma Assert (for all I in Integer =>
                          (if M_Contains (T.Left, I) then M_Contains (T, I)));
         pragma Assert (for all I in Integer =>
                          (if M_Contains (T.Right, I) then M_Contains (T, I)));
         return T.Data < V and T.Left < V and T.Right < V;
      end if;
   end "<";

   function Sorted (T : access constant Tree) return Boolean is
     (if T = null then True
      else T.Left < T.Data and then T.Data < T.Right
        and then Sorted (T.Left) and then Sorted (T.Right))
   with Annotate => (GNATprove, Terminating),
     Ghost;

   function Contains (T : access constant Tree; V : Integer) return Boolean with
     Pre  => Sorted (T),
     Post => Contains'Result = M_Contains (T, V)
   is
      X : access constant Tree := T;
   begin
      while X /= null loop
         pragma Loop_Invariant (Sorted (X));
         pragma Loop_Invariant (M_Contains (T, V) = M_Contains (X, V));
         if X.Data = V then
            return True;
         elsif V < X.Data then
            X := X.Left;
         else
            X := X.Right;
         end if;
      end loop;
      return False;
   end Contains;

   type Int_Option (Present : Boolean := False) is record
      case Present is
         when True  => Value : Integer;
         when False => null;
      end case;
   end record;

   function "<" (V : Int_Option; T : access constant Tree) return Boolean is
     (if V.Present then V.Value < T else True)
   with Ghost;

   function "<" (T : access constant Tree; V : Int_Option) return Boolean is
     (if V.Present then T < V.Value else True)
   with Ghost;

   function "<" (V : Int_Option; I : Integer) return Boolean is
     (if V.Present then V.Value < I else True)
   with Ghost;

   function "<" (I : Integer; V : Int_Option) return Boolean is
     (if V.Present then I < V.Value else True)
   with Ghost;

   package Int_Sets is new Ada.Containers.Functional_Sets (Integer);
   type Int_Set is new Int_Sets.Set;

   function Size (T : access constant Tree) return Natural is
     (if T = null then 0
      elsif Size (T.Left) < Natural'Last - Size (T.Right)
      then Size (T.Left) + Size (T.Right) + 1
      else Natural'Last)
   with Annotate => (GNATprove, Terminating),
     Ghost;

   function All_V (T : access constant Tree) return Int_Set with
     Ghost,
     Annotate => (GNATprove, Terminating),
     Pre  => Size (T) < Natural'Last,
     Post => Length (All_V'Result) <= Count_Type (Size (T))
     and then (for all I in Integer => M_Contains (T, i) = Contains (All_V'Result, I))
   is
   begin
      return S : Int_Set do
         if T = null then
            return;
         end if;

         S := Union (All_V (T.Left), All_V (T.Right));
         if not Contains (S, T.Data) then
            S := Add (S, T.Data);
         end if;
      end return;
   end All_V;

   procedure Insert (T : in out Tree_Acc; V : Integer) with
     Pre  => Sorted (T) and Size (T) < Natural'Last,
     Post => Sorted (T) and M_Contains (T, V)
     and (for all I in Integer =>
            M_Contains (T, I) = (I = V or Contains (All_V (T)'Old, I)))
   is
      L, H : Int_Option := (Present => False) with Ghost;
   begin
      if T = null then
         pragma Assert (Sorted (T));
         T := new Tree'(Data  => V,
                        Left  => null,
                        Right => null);
         return;
      end if;

      declare
         T_Old : constant Int_Set := All_V (T) with Ghost;
         X     : access Tree := T;
         Seen  : Int_Set with Ghost;
      begin
         loop
            pragma Loop_Invariant (X /= null);
            pragma Loop_Invariant (Sorted (X));
            pragma Loop_Invariant (X < H and L < X);
            pragma Loop_Invariant (V < H and L < V);
            pragma Loop_Invariant
              (Length (Seen) <= Count_Type (Size (X)'Loop_Entry - Size (X)));
            pragma Loop_Invariant
              (for all I in Integer =>
                 (if M_Contains (X, I) then Contains (T_Old, I)));
            pragma Loop_Invariant
              (for all I of Seen => Contains (T_Old, I));
            pragma Loop_Invariant
              (for all I of T_Old => Contains (Seen, I) or M_Contains (X, I));
            pragma Loop_Invariant
              (for all I of Seen => not M_Contains (X, I));

            pragma Loop_Invariant
              (for all I in Integer =>
                 (if M_Contains (At_End_Borrow (X), I)
                  then M_Contains (At_End_Borrow (T), I)));
            pragma Loop_Invariant
              (for all I of Seen => M_Contains (At_End_Borrow (T), I));
            pragma Loop_Invariant
              (for all I in Integer =>
                 (if M_Contains (At_End_Borrow (T), I)
                  then Contains (Seen, I) or M_Contains (At_End_Borrow (X), I)));
            pragma Loop_Invariant
              (if Sorted (At_End_Borrow (X))
                 and then At_End_Borrow (X) < H and then L < At_End_Borrow (X)
               then Sorted (At_End_Borrow (T)));

            if X.Data = V then
               return;
            elsif V < X.Data then
               if X.Left = null then
                  X.Left := new Tree'(Data  => V,
                                      Left  => null,
                                      Right => null);
                  return;
               else
                  H := (Present => True, Value => X.Data);
                  Seen := Union (Seen, Add (All_V (X.Right), X.Data));
                  X := X.Left;
               end if;
            else
               if X.Right = null then
                  X.Right := new Tree'(Data  => V,
                                       Left  => null,
                                       Right => null);
                  return;
               else
                  L := (Present => True, Value => X.Data);
                  Seen := Union (Seen, Add (All_V (X.Left), X.Data));
                  X := X.Right;
               end if;
            end if;
         end loop;
      end;
   end Insert;

begin
   null;
end Binary_Search;
