with Private_Ptr; use Private_Ptr;

package Client is
   type U is private;
private
   type U is new V(100);
end Client;
