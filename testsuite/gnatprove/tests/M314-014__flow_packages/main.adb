with Initialized;
with Uninitialized;

procedure Main
   with SPARK_Mode,
        Global  => (Input  => Initialized.State,
                    Output => Uninitialized.State),
        Depends => (Uninitialized.State => Initialized.State)
is
begin
   Uninitialized.Set (Initialized.Get);
end Main;
