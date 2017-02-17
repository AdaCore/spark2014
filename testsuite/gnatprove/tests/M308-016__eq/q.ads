package Q is
   type T (B : Boolean) is record
      case B is
         when True =>
            A : Integer;
         when False =>
            C : Boolean;
      end case;
   end record;

   function Change (X : T) return T;--   with
     --  Post =>
     --    (Change'Result.B = X.B
     --       and then
     --     (case X.B is
     --       when True =>
     --         Change'Result.A = 0,
     --       when False =>
     --         Change'Result.C = False));

   procedure Update (X, Y : in out T) with
     Pre => X = Y,
     Post => X = Y;
end Q;
