
// Regression2.dfy

method Main()
{
}

module NativeTypes {
  newtype uint64 = int
}

module ConversionModule {
  predicate Uint64ToBytes(u: uint64)
  {
    true
  }

  import opened NativeTypes
}

abstract module AppStateMachine_s {

  import opened NativeTypes
}

module AppStateMachine_i refines AppStateMachine_s {
  predicate F(response: uint64)
  {
    ConversionModule.Uint64ToBytes(response)
  }

  import ConversionModule
}
