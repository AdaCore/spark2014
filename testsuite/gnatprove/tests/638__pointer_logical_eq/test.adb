procedure Test with SPARK_Mode is

   type R (D : Boolean := False) is record
      case D is
      when True => I : Integer;
      when False => null;
      end case;
   end record;

   type L_Cell;
   type L is access L_Cell;
   type L_Cell is record
      V : R;
      N : L;
   end record;

   X : L;

   procedure P (X : not null L) is
   begin
      if X.V.D then
         X.V.I := 1;
      end if;
   end P;

   function My_Eq (X, Y : L) return Boolean is
     ((X = null) = (Y = null)
      and then (if X /= null then X.V = Y.V and then My_Eq (X.N, Y.N)))
     with Annotate => (GNATprove, Logical_Equal),
     Subprogram_Variant => (Structural => X);
begin
   null;
end Test;
