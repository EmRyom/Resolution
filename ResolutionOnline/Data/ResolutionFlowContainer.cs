namespace ResolutionOnline.Data
{
    public class ResolutionFlowContainer
    {
        public ResolutionFlow? Value { get; set; }
        public event Action OnStateChange;
        public void SetValue(ResolutionFlow resolutionFlow)
        {
            Value = resolutionFlow;
            NotifyStateChanged();
        }
        private void NotifyStateChanged() => OnStateChange?.Invoke();
    }
}
