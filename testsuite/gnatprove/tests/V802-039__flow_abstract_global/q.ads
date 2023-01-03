with P;

package Q is
   pragma Elaborate_Body;
   type TT is new P.T with record
      CC : Integer;
   end record;

   Y : Integer;

   procedure A (X : TT) with Global  => (Proof_In => Y);
   procedure B (X : TT) with Depends => (null => (X, Y));
end;
