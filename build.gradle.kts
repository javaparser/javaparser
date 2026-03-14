plugins {
    id("test-report-aggregation")
}

reporting {
    reports {
        val testAggregateTestReport by creating(AggregateTestReport::class) {
            testSuiteName = "test"
        }
    }
}
