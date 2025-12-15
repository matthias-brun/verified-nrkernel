// MIT License
//
// Copyright (c) 2025 Paper #409 Authors, ASPLOS'26.
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

pub struct Stats {
    #[allow(dead_code)]
    pub min: i64,
    #[allow(dead_code)]
    pub med: i64,
    #[allow(dead_code)]
    pub avg: i64,
    #[allow(dead_code)]
    pub max: i64,
    #[allow(dead_code)]
    pub p99: i64,
    #[allow(dead_code)]
    pub p95: i64,
    #[allow(dead_code)]
    pub var: i64,
    #[allow(dead_code)]
    pub std: i64,
    #[allow(dead_code)]
    pub num: usize,
}

impl From<&[i64]> for Stats {
    fn from(stats: &[i64]) -> Self {
        let mut datapoints = stats.to_vec();
        datapoints.sort();
        let num_datapoints = datapoints.len();

        if num_datapoints == 0 {
            Self {
                min: 0,
                med: 0,
                avg: 0,
                max: 0,
                p99: 0,
                p95: 0,
                var: 0,
                std: 0,
                num: 0,
            }
        } else {
            // detect outliers

            let q1 = datapoints[num_datapoints / 4];
            let q3 = datapoints[num_datapoints * 3 / 4];
            let iqr = q3 - q1;
            let iqr_delta = 2 * iqr; // + (iqr >> 1); // 1.5 * iqr;
            let upper_fence = q3 + iqr_delta; // q3 + 1.5 * iqr
            let lower_fence = if q1 < iqr_delta {
                0
            } else {
                q1 - iqr_delta // q1 - 1.5 * iqr
            };
            let data = if datapoints.len() > 10 {
                datapoints
                    .into_iter()
                    .filter(|x| *x <= upper_fence && *x >= lower_fence)
                    .collect::<Vec<i64>>()
            } else {
                datapoints
            };

            let num = data.len();
            let sum = data.iter().sum::<i64>() as i64;
            let avg = sum / num as i64;

            let var = data.iter().map(|x| (x - avg) * (x - avg)).sum::<i64>() as i64 / num as i64;
            let std = (var as f64).sqrt() as i64;
            Self {
                min: *data.first().unwrap(),
                med: data[num / 2],
                avg,
                max: *data.last().unwrap(),
                p99: data[num * 99 / 100],
                p95: data[num * 95 / 100],
                var,
                std,
                num,
            }
        }
    }
}
