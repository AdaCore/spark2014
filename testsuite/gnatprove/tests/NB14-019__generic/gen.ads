generic
   Bounded : Boolean := True;
package Gen with Initializes => (Y => Bounded) is
   Y : Boolean;

   procedure P;
end Gen;
