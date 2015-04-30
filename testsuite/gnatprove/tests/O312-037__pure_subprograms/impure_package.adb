with State;

package body Impure_Package is

   function Impure_Function (X : Integer) return Integer is
   begin
      return X + State.Y;
   end Impure_Function;

end Impure_Package;
