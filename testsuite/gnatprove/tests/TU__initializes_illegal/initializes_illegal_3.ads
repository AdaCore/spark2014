with Initializes_Illegal_3_Helper;
use  Initializes_Illegal_3_Helper;

package Initializes_Illegal_3
  --  TU: 3. The ``name`` of each ``initialization_item`` in the Initializes
  --  aspect definition for a package shall denote a state abstraction of the
  --  package or an entire variable declared immediately within the visible
  --  part of the package.

  --  TU: 4. Each ``name`` in the ``input_list`` shall denote an entire
  --  variable or a state abstraction but shall not denote an entity declared
  --  in the package with the ``aspect_specification`` containing the
  --  Initializes aspect.

  --  TU: 5. Each entity in a single ``input_list`` shall be distinct.

  --  TU: 7. The Initializes aspect of a package has visibility of the
  --  declarations occurring immediately within the visible part of the
  --  package.
  with SPARK_Mode,
       Abstract_State => (S1, S2),
       Initializes    => (Rec.A,  --  Not entire variable

                          PrivVar,  --  Not visible

                          Emb.SS,  --  Not directly within visible part

                          Emb.XX,  --  Not directly within visible part

                          S1 => (Rec, S2, Emb.SS, Emb.XX),
                          --  All entities of the input_list are declared
                          --  within the visible part of the package

                          S2 => (SH, Var_H, SH, Var_H))
                          --  Not distinct input_list entities
is
   type RecordT is record
      A, B : Integer;
   end record;

   Rec : RecordT;

   package Emb
     with Abstract_State => SS
   is
      XX : Integer;
   end Emb;
private
   PrivVar : Integer;
end Initializes_Illegal_3;
