with Other;
pragma Elaborate_All (Other);

package Generate_Initializes is
   A : Integer := 0;

   package Nested is new Other (5);
end Generate_Initializes;
