with State;

package body Impure_Package is

   function Pure_Function (X : Integer) return Integer is
   begin
      return X + State.Y;
   end Pure_Function;

end Impure_Package;
