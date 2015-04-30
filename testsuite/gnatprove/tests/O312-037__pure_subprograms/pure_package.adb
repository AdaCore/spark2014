with State;

package body Pure_Package is

   function Pure_Function (X : Integer) return Integer is
   begin
      return X + State.Y;
   end Pure_Function;

end Pure_Package;
