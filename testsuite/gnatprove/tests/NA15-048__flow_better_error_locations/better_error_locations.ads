with A, B, C;

package Better_Error_Locations is
   procedure P (X : out Integer)
     with Global  => (A.State, B.State, C.State),
          Depends => (X => (A.State, B.State, C.State));
end Better_Error_Locations;
