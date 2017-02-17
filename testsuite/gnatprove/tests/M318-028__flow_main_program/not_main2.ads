with Generics;
pragma Elaborate_All(Generics);

package Not_Main2 is
   procedure Not_Main_Generic_Instantiation is new Generics.Does_Nothing (Elem => Integer);
end Not_Main2;
