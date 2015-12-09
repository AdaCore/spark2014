generic
   Bounded : Boolean;
package Gen
  with Initializes => (Y => Bounded)
is
   Y : Boolean;

   function Get_Bounded return Boolean
     with Global => Bounded;

   procedure P
     with Global => (Input  => Bounded,
                     Output => Y),
          Post   => Y = not Bounded;
end Gen;
