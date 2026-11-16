/* Register the placement-aware synthesis commands. */
#include "pa.h"
#include "paPlace.h"
ABC_NAMESPACE_IMPL_START
void Pa_Init(Abc_Frame_t *frame)
{
    Pa_RegisterPlacementCommands(frame);
    Pa_RegisterSynthesisCommands(frame);
}
void Pa_End(Abc_Frame_t *)
{
    Pa_ManClearPlacement();
}
ABC_NAMESPACE_IMPL_END
